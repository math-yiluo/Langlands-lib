import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions.SumProd

/-! # Actual induced topological spaces -/

noncomputable section

universe u v w

namespace Langlands.TopologicalInduction

open Topology

variable {G : Type u} [Group G] (H : Subgroup G) (X : Type v) [MulAction H X]

/-- Representatives for the balanced quotient, with a separate subgroup action. -/
def Representatives (_H : Subgroup G) (X : Type v) := G × X

instance : MulAction H (Representatives H X) where
  smul h p := (p.1 * (h : G)⁻¹, h • p.2)
  one_smul p := by
    change (p.1 * ((1 : H) : G)⁻¹, (1 : H) • p.2) = p
    simp
    rfl
  mul_smul h k p := by
    change (p.1 * (((h * k : H) : G))⁻¹, (h * k) • p.2) =
      ((p.1 * (k : G)⁻¹) * (h : G)⁻¹, h • k • p.2)
    simp [mul_assoc, mul_smul]

/-- The actual balanced quotient `G ×_H X`. -/
def Space := Quotient (MulAction.orbitRel H (Representatives H X))

variable {X}

/-- The class of a representative. -/
def mk (g : G) (x : X) : Space H X :=
  Quotient.mk (MulAction.orbitRel H (Representatives H X)) (g, x)

variable {H}

theorem mk_eq_mk_iff (g k : G) (x y : X) :
    mk H g x = mk H k y ↔
      ∃ h : H, g = k * (h : G)⁻¹ ∧ x = h • y := by
  constructor
  · intro e
    obtain ⟨h, hh⟩ := Quotient.exact e
    exact ⟨h, (congrArg Prod.fst hh).symm, (congrArg Prod.snd hh).symm⟩
  · rintro ⟨h, rfl, rfl⟩
    exact Quotient.sound ⟨h, rfl⟩

@[simp]
theorem mk_subgroup_smul (h : H) (g : G) (x : X) :
    mk H (g * (h : G)⁻¹) (h • x) = mk H g x :=
  Quotient.sound ⟨h, rfl⟩

theorem mk_balance (h : H) (g : G) (x : X) :
    mk H (g * (h : G)) x = mk H g (h • x) := by
  apply (mk_eq_mk_iff _ _ _ _).2
  exact ⟨h⁻¹, by simp, by simp⟩

private def leftMul (a : G) (p : Representatives H X) : Representatives H X :=
  (a * p.1, p.2)

private theorem leftMul_rel (a : G) {p q : Representatives H X}
    (e : MulAction.orbitRel H (Representatives H X) p q) :
    MulAction.orbitRel H (Representatives H X) (leftMul a p) (leftMul a q) := by
  obtain ⟨h, rfl⟩ := e
  refine ⟨h, ?_⟩
  change ((a * q.1) * (h : G)⁻¹, h • q.2) =
    (a * (q.1 * (h : G)⁻¹), h • q.2)
  rw [mul_assoc]

/-- Left multiplication of representatives gives the full group action. -/
instance : MulAction G (Space H X) where
  smul a := Quotient.map' (leftMul a) (fun _ _ => leftMul_rel a)
  one_smul z := by
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨1, by change (p.1 * ((1 : H) : G)⁻¹, (1 : H) • p.2) =
        (1 * p.1, p.2); simp⟩
  mul_smul a b z := by
    induction z using Quotient.inductionOn with
    | h p =>
      change mk H ((a * b) * p.1) p.2 = mk H (a * (b * p.1)) p.2
      rw [mul_assoc]

@[simp]
theorem smul_mk (a g : G) (x : X) :
    a • mk H g x = mk H (a * g) x := rfl

/-- The distinguished copy of the original subgroup space. -/
def unit (H : Subgroup G) {X : Type v} [MulAction H X] (x : X) : Space H X :=
  mk H 1 x

@[simp]
theorem smul_unit (g : G) (x : X) : g • unit H x = mk H g x := by
  simp [unit]

theorem unit_injective : Function.Injective (unit H : X → Space H X) := by
  intro x y e
  obtain ⟨h, hg, hx⟩ := (mk_eq_mk_iff 1 1 x y).1 e
  have hv : (h : G) = 1 := inv_eq_one.mp (by simpa using hg.symm)
  have hh : h = 1 := Subtype.ext hv
  simpa [hh] using hx

@[simp]
theorem unit_subgroup_smul (h : H) (x : X) :
    unit H (h • x) = (h : G) • unit H x := by
  simpa [unit] using (mk_balance h 1 x).symm

variable {Y : Type w} [MulAction G Y]

/-- Extend a subgroup-equivariant map by the actual balanced quotient. -/
def lift (φ : X → Y) (hφ : ∀ (h : H) (x : X), φ (h • x) = (h : G) • φ x) :
    Space H X → Y :=
  Quotient.lift (fun p : Representatives H X => p.1 • φ p.2) (by
    intro p q e
    obtain ⟨h, rfl⟩ := e
    change (q.1 * (h : G)⁻¹) • φ (h • q.2) = q.1 • φ q.2
    rw [hφ, mul_smul, inv_smul_smul])

@[simp]
theorem lift_mk (φ : X → Y) (hφ) (g : G) (x : X) :
    lift φ hφ (mk H g x) = g • φ x := rfl

@[simp]
theorem lift_unit (φ : X → Y) (hφ) (x : X) :
    lift φ hφ (unit H x) = φ x := by simp [unit]

theorem lift_smul (φ : X → Y) (hφ) (g : G) (z : Space H X) :
    lift φ hφ (g • z) = g • lift φ hφ z := by
  induction z using Quotient.inductionOn with
  | h p =>
    change (g * p.1) • φ p.2 = g • p.1 • φ p.2
    rw [mul_smul]

theorem lift_unique (φ : X → Y) (hφ) (f : Space H X → Y)
    (hf : ∀ (g : G) (z : Space H X), f (g • z) = g • f z)
    (hunit : ∀ x, f (unit H x) = φ x) : f = lift φ hφ := by
  funext z
  induction z using Quotient.inductionOn with
  | h p =>
    change f (mk H p.1 p.2) = lift φ hφ (mk H p.1 p.2)
    rw [← smul_unit, hf, hunit]
    simp

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [ContinuousSMul H X]

instance : TopologicalSpace (Representatives H X) :=
  inferInstanceAs (TopologicalSpace (G × X))

instance : ContinuousConstSMul H (Representatives H X) where
  continuous_const_smul h := by
    change Continuous (fun p : G × X => (p.1 * (h : G)⁻¹, h • p.2))
    exact (continuous_fst.mul_const _).prodMk ((continuous_const_smul h).comp continuous_snd)

instance : TopologicalSpace (Space H X) :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel H (Representatives H X))))

theorem isOpenQuotientMap_mk :
    IsOpenQuotientMap (fun p : Representatives H X => mk H p.1 p.2) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem continuous_mk : Continuous (fun p : G × X => mk H p.1 p.2) :=
  isOpenQuotientMap_mk.continuous

instance : ContinuousSMul G (Space H X) where
  continuous_smul := by
    have hq := (IsOpenQuotientMap.id (X := G)).prodMap
      (isOpenQuotientMap_mk (H := H) (X := X))
    apply hq.continuous_comp_iff.mp
    change Continuous (fun p : G × (G × X) => mk H (p.1 * p.2.1) p.2.2)
    exact continuous_mk.comp
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))

theorem continuous_unit : Continuous (unit H : X → Space H X) :=
  continuous_mk.comp (continuous_const.prodMk continuous_id)

/-- The involution on subgroup representatives used to exhibit the unit as open. -/
def subgroupTwist : H × X ≃ₜ H × X where
  toFun p := (p.1⁻¹, p.1 • p.2)
  invFun p := (p.1⁻¹, p.1 • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.inv.prodMk (continuous_fst.smul continuous_snd)
  continuous_invFun := continuous_fst.inv.prodMk (continuous_fst.smul continuous_snd)

/-- For an open subgroup the distinguished copy is an open map. -/
theorem isOpenMap_unit (hH : IsOpen (H : Set G)) :
    IsOpenMap (unit H : X → Space H X) := by
  have hi : IsOpenMap (Prod.map (Subtype.val : H → G) (id : X → X)) :=
    hH.isOpenEmbedding_subtypeVal.isOpenMap.prodMap IsOpenMap.id
  have ho := (isOpenQuotientMap_mk (H := H) (X := X)).isOpenMap.comp
    (hi.comp (subgroupTwist (H := H) (X := X)).isOpenMap)
  have he : (fun p : H × X =>
      mk H ((p.1⁻¹ : H) : G) (p.1 • p.2)) = unit H ∘ Prod.snd := by
    funext p
    simpa [unit] using (mk_subgroup_smul p.1 1 p.2)
  change IsOpenMap (fun p : H × X =>
    mk H ((p.1⁻¹ : H) : G) (p.1 • p.2)) at ho
  rw [he] at ho
  exact IsOpenMap.of_comp continuous_snd Prod.snd_surjective ho

/-- The distinguished copy of a continuous open-subgroup space is an open embedding. -/
theorem isOpenEmbedding_unit (hH : IsOpen (H : Set G)) :
    IsOpenEmbedding (unit H : X → Space H X) :=
  .of_continuous_injective_isOpenMap continuous_unit unit_injective (isOpenMap_unit hH)

variable [TopologicalSpace Y] [ContinuousSMul G Y]

omit [IsTopologicalGroup G] [ContinuousSMul H X] in
theorem continuous_lift (φ : X → Y) (hφ) (hcont : Continuous φ) :
    Continuous (lift φ hφ : Space H X → Y) :=
  (continuous_fst.smul (hcont.comp continuous_snd)).quotient_lift _

/-- The continuous extension, retaining its explicit evaluation formula. -/
def extend (φ : C(X, Y)) (hφ : ∀ (h : H) (x : X), φ (h • x) = (h : G) • φ x) :
    C(Space H X, Y) :=
  ⟨lift φ hφ, continuous_lift φ hφ φ.continuous⟩

/-- Restriction to the unit and continuous extension are mutually inverse on
actual continuous equivariant maps. -/
def equivariantMapEquiv :
    {f : C(Space H X, Y) // ∀ (g : G) (z : Space H X), f (g • z) = g • f z} ≃
      {φ : C(X, Y) // ∀ (h : H) (x : X), φ (h • x) = (h : G) • φ x} where
  toFun f := ⟨f.1.comp ⟨unit H, continuous_unit⟩, by
    intro h x
    change f.1 (unit H (h • x)) = (h : G) • f.1 (unit H x)
    rw [unit_subgroup_smul, f.2]⟩
  invFun φ := ⟨extend φ.1 φ.2, lift_smul φ.1 φ.2⟩
  left_inv f := by
    apply Subtype.ext
    apply ContinuousMap.ext
    exact congrFun (lift_unique (fun x => f.1 (unit H x))
      (fun h x => by rw [unit_subgroup_smul, f.2]) f.1 f.2 (fun _ => rfl)).symm
  right_inv φ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    exact fun x => lift_unit φ.1 φ.2 x

end Topology

end Langlands.TopologicalInduction
