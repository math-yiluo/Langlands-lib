import Langlands.Representation.Clifford.Types

/-!
# Types lying over classes of a normal subgroup
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uV uW

section Defs

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Continuous irreducible finite-dimensional complex representations. -/
abbrev IsTypeRep (A : FiniteRepresentation.{0, uG, uW} ℂ G) : Prop :=
  A.IsContinuous ∧ A.IsIrreducible

variable (G) in
/-- Objects underlying the type classes. -/
abbrev TypeObj := {A : FiniteRepresentation.{0, uG, uW} ℂ G // IsTypeRep A}

variable (G) in
/-- Isomorphism classes of continuous irreducible representations. -/
abbrev TypeClasses := IsomorphismClassesWith.{0, uG, uW} (IsTypeRep (G := G))

/-- The class of a type object. -/
abbrev typeClass (B : TypeObj.{uG, uW} G) : TypeClasses.{uG, uW} G := Quotient.mk _ B

theorem typeClass_eq_iff (B B' : TypeObj.{uG, uW} G) :
    typeClass B = typeClass B' ↔
      Nonempty (Representation.Equiv B.1.representation B'.1.representation) :=
  Quotient.eq

variable (N : Subgroup G)

/-- There is a nonzero intertwiner from the restriction of `B` to `N` to `A`. -/
def Over (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N) : Prop :=
  ∃ T : IntertwiningMap (B.1.representation.comp N.subtype) A.1.representation, T ≠ 0

/-- A type class lies over a class of `N` if some representatives are related by `Over`. -/
def LiesOver (x : TypeClasses.{uG, uW} G) (c : OpenKernelIrreducibleClasses.{uG, uW} N) : Prop :=
  ∃ (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N),
    typeClass B = x ∧ wildClass A = c ∧ Over N B A

variable {N}

theorem over_of_equiv {B B' : TypeObj.{uG, uW} G} {A A' : WildObj.{uG, uW} N}
    (eB : Representation.Equiv B.1.representation B'.1.representation)
    (eA : Representation.Equiv A.1.representation A'.1.representation)
    (h : Over N B A) : Over N B' A' := by
  obtain ⟨T, hT⟩ := h
  let eB' : Representation.Equiv (B.1.representation.comp N.subtype)
      (B'.1.representation.comp N.subtype) :=
    Representation.Equiv.mk eB.toLinearEquiv fun n => eB.isIntertwining' (n : G)
  refine ⟨(eA.toIntertwiningMap.comp T).comp eB'.symm.toIntertwiningMap, fun h0 => hT ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 := congrArg (fun F : IntertwiningMap _ _ => eA.symm (F (eB' v))) h0
  simpa using h1

theorem liesOver_iff (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N) :
    LiesOver N (typeClass B) (wildClass A) ↔ Over N B A := by
  constructor
  · rintro ⟨B', A', hB, hA, h⟩
    obtain ⟨eB⟩ := (typeClass_eq_iff _ _).mp hB
    obtain ⟨eA⟩ := (wildClass_eq_iff _ _).mp hA
    exact over_of_equiv eB eA h
  · intro h
    exact ⟨B, A, rfl, rfl, h⟩

end Defs

section Comp

variable {G : Type uG} [Group G] {G' : Type*} [Group G']
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- An equivalence stays an equivalence after precomposition with a homomorphism. -/
def equivComp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (f : G' →* G) : Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' (f g)

theorem twist_one (ρ : Representation ℂ G V) : Langlands.twist 1 ρ = ρ := by
  ext g v
  change ((1 : G →* ℂˣ) g : ℂ) • ρ g v = ρ g v
  simp

end Comp

section Pullback

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation `g ↦ h g h⁻¹`, as a continuous automorphism. -/
def conjCts (h : G) : G ≃ₜ* G where
  toFun g := h * g * h⁻¹
  invFun g := h⁻¹ * g * h
  left_inv g := by group
  right_inv g := by group
  map_mul' x y := by group
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem conjCts_apply (h g : G) : conjCts h g = h * g * h⁻¹ := rfl

/-- Pullback of a type along a continuous automorphism. -/
def typeObjPullback (α : G ≃ₜ* G) (B : TypeObj.{uG, uW} G) : TypeObj.{uG, uW} G :=
  ⟨FiniteRepresentation.of (B.1.representation.comp α.toMulEquiv.toMonoidHom), by
      let _ : TopologicalSpace (Module.End ℂ B.1) := moduleTopology ℂ (Module.End ℂ B.1)
      have h : Continuous B.1.representation := B.2.1
      exact h.comp α.continuous, by
      have := B.2.2
      exact Langlands.CuspidalSupport.isIrreducible_comp_of_surjective _ _ α.surjective⟩

/-- Pullback of type classes along a continuous automorphism. -/
def typePullback (α : G ≃ₜ* G) : TypeClasses.{uG, uW} G → TypeClasses.{uG, uW} G :=
  Quotient.map (typeObjPullback α) fun _ _ ⟨e⟩ =>
    ⟨Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' (α g)⟩

omit [IsTopologicalGroup G] in
theorem typePullback_mk (α : G ≃ₜ* G) (B : TypeObj.{uG, uW} G) :
    typePullback α (typeClass B) = typeClass (typeObjPullback α B) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A representation precomposed with an inner automorphism is equivalent to itself. -/
def conjCompEquiv {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : G) (f : G →* G) (hf : ∀ g, f g = h * g * h⁻¹) :
    Representation.Equiv (ρ.comp f) ρ where
  toLinearEquiv := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom h⁻¹)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change ρ h⁻¹ (ρ (f g) v) = ρ g (ρ h⁻¹ v)
    rw [hf, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

/-- Inner automorphisms act trivially on type classes. -/
theorem typeClass_pullback_conj (h : G) (B : TypeObj.{uG, uW} G) :
    typeClass (typeObjPullback (conjCts h) B) = typeClass B :=
  (typeClass_eq_iff _ _).mpr
    ⟨conjCompEquiv B.1.representation h (conjCts h).toMulEquiv.toMonoidHom fun _ => rfl⟩

/-- Pullback along the composite of an inner automorphism and `α` agrees with pullback along
`α`. -/
theorem typePullback_conj_trans (h : G) (α : G ≃ₜ* G) (x : TypeClasses.{uG, uW} G) :
    typePullback ((conjCts h).trans α) x = typePullback α x := by
  induction x using Quotient.inductionOn with
  | h B =>
    change typeClass (typeObjPullback ((conjCts h).trans α) B) = typeClass (typeObjPullback α B)
    exact typeClass_pullback_conj h (typeObjPullback α B)

section WildPullback

variable {N : Subgroup G} [N.Normal]

omit [IsTopologicalGroup G] [N.Normal] in
theorem continuous_restrictAut (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) :
    Continuous (restrictAut α.toMulEquiv hN) :=
  (α.continuous.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] [N.Normal] in
theorem restrictAut_surjective (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) :
    Function.Surjective (restrictAut α.toMulEquiv hN) := by
  intro n
  refine ⟨⟨α.symm n, (hN _).mpr (by simp)⟩, Subtype.ext ?_⟩
  change α (α.symm n) = n
  simp

/-- Pullback of an object of `N` along an automorphism preserving `N`. -/
def wildObjPullback (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) (A : WildObj.{uG, uW} N) :
    WildObj.{uG, uW} N :=
  ⟨restrict (restrictAut α.toMulEquiv hN) A.1, by
    have := A.2.1
    exact Langlands.CuspidalSupport.isIrreducible_comp_of_surjective A.1.representation _
      (restrictAut_surjective α hN), by
    change IsOpen ((restrictAut α.toMulEquiv hN) ⁻¹' (A.1.representation.ker : Set N))
    exact A.2.2.preimage (continuous_restrictAut α hN)⟩

/-- Pullback of classes of `N` along an automorphism preserving `N`. -/
def wildPullback (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) :
    OpenKernelIrreducibleClasses.{uG, uW} N → OpenKernelIrreducibleClasses.{uG, uW} N :=
  Quotient.map (wildObjPullback α hN) fun _ _ ⟨e⟩ => ⟨restrictEquiv _ e⟩

omit [IsTopologicalGroup G] [N.Normal] in
theorem wildPullback_mk (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) (A : WildObj.{uG, uW} N) :
    wildPullback α hN (wildClass A) = wildClass (wildObjPullback α hN A) := rfl

omit [IsTopologicalGroup G] [N.Normal] in
theorem symm_mem (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) (x : G) :
    x ∈ N ↔ α.symm x ∈ N := by
  rw [hN (α.symm x)]
  simp

omit [IsTopologicalGroup G] [N.Normal] in
/-- Pulling back along the inverse undoes the pullback. -/
theorem wildPullback_symm_wildPullback (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N)
    (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    wildPullback α.symm (symm_mem α hN) (wildPullback α hN c) = c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply (wildClass_eq_iff _ _).mpr
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    apply LinearMap.ext
    intro v
    change A.1.representation (restrictAut α.toMulEquiv hN
      (restrictAut α.symm.toMulEquiv (symm_mem α hN) n)) v = A.1.representation n v
    congr 2
    apply Subtype.ext
    change α (α.symm n) = n
    simp

omit [IsTopologicalGroup G] [N.Normal] in
theorem wildPullback_injective (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) :
    Function.Injective (wildPullback.{uG, uW} α hN) := fun c c' h => by
  rw [← wildPullback_symm_wildPullback α hN c, ← wildPullback_symm_wildPullback α hN c', h]

/-- Pullback intertwines the conjugation actions: the pullback of `g • c` is `α⁻¹ g` acting on
the pullback of `c`. -/
theorem wildPullback_smul (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) (g : G)
    (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    wildPullback α hN (g • c) = α.symm g • wildPullback α hN c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply (wildClass_eq_iff _ _).mpr
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    apply LinearMap.ext
    intro v
    change A.1.representation (MulAut.conjNormal g⁻¹ (restrictAut α.toMulEquiv hN n)) v =
      A.1.representation (restrictAut α.toMulEquiv hN (MulAut.conjNormal (α.symm g)⁻¹ n)) v
    congr 2
    apply Subtype.ext
    have hg : ((α : G ≃* G) (α.symm g) : G) = g := α.apply_symm_apply g
    simp [restrictAut, hg]

omit [IsTopologicalGroup G] [N.Normal] in
theorem wildPullback_trans (α β : G ≃ₜ* G) (hα : ∀ x, x ∈ N ↔ α x ∈ N)
    (hβ : ∀ x, x ∈ N ↔ β x ∈ N) (hαβ : ∀ x, x ∈ N ↔ (α.trans β) x ∈ N)
    (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    wildPullback (α.trans β) hαβ c = wildPullback α hα (wildPullback β hβ c) := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply (wildClass_eq_iff _ _).mpr
    exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => rfl⟩

/-- Pullback along an inner automorphism is the conjugation action by the inverse. -/
theorem wildPullback_conjCts (h : G) (hN : ∀ x, x ∈ N ↔ conjCts h x ∈ N)
    (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    wildPullback (conjCts h) hN c = h⁻¹ • c := by
  induction c using Quotient.inductionOn with
  | h A =>
    apply (wildClass_eq_iff _ _).mpr
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    apply LinearMap.ext
    intro v
    change A.1.representation (restrictAut (conjCts h).toMulEquiv hN n) v =
      A.1.representation (MulAut.conjNormal h⁻¹⁻¹ n) v
    congr 2
    apply Subtype.ext
    simp only [restrictAut, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv, MulAut.conjNormal_apply]
    rfl

/-- An automorphism preserving `N` whose pullback fixes a class preserves the stabilizer of the
class. -/
theorem mem_stabilizer_iff_of_fixed (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N)
    {c : OpenKernelIrreducibleClasses.{uG, uW} N} (hc : wildPullback α hN c = c) (x : G) :
    x ∈ MulAction.stabilizer G c ↔ α x ∈ MulAction.stabilizer G c := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro hx
    apply wildPullback_injective α hN
    rw [wildPullback_smul, hc, ContinuousMulEquiv.symm_apply_apply, hx]
  · intro hx
    have h1 := congrArg (wildPullback α hN) hx
    rw [wildPullback_smul, hc, ContinuousMulEquiv.symm_apply_apply] at h1
    exact h1

end WildPullback

end Pullback

end Langlands.Clifford
