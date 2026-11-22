import Langlands.AbelianScheme.Tate.FiniteTorsionStructure
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Langlands.Geometry.FormalGroup.PDivisibleGroupEtaleLevels
import Langlands.Geometry.FormalGroup.PDivisibleGroupTatePadic

/-! # The finite-level geometric rank of a p-divisible group -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open CommGroupScheme

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p)

/-- The rank of the actual finite level as a scheme morphism agrees with the
coordinate-algebra rank defining height. -/
theorem finiteLevel_finrank_eq_levelRank (n : ℕ) (x : Spec R) :
    (G.inclusions.obj n).X.hom.finrank x = G.levelRank n x := by
  let X := (G.inclusions.obj n).X
  have : IsFinite X.hom := (G.finiteLocallyFree n).1
  have : Flat X.hom := (G.finiteLocallyFree n).2.1
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let φ : R ⟶ Γ(X.left, ⊤) := (Scheme.ΓSpecIso R).inv ≫ X.hom.appTop
  have hφ : Spec.map φ = X.left.isoSpec.inv ≫ X.hom := by
    dsimp only [φ]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have hfinite : φ.hom.Finite :=
    RingHom.Finite.comp X.hom.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2)
  have hflat : φ.hom.Flat :=
    RingHom.Flat.comp
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))
      X.hom.flat_appTop
  change X.hom.finrank x = _
  rw [← Scheme.Hom.finrank_comp_left_of_isIso X.left.isoSpec.inv X.hom, ← hφ,
    Scheme.Hom.finrank_SpecMap_eq_finrank hfinite hflat]
  rfl

private abbrev affineLevelPoints (A : CommAlgCat.{u} R) (n : ℕ) :=
  (G.schematicTateTestDiagram (affineTest A)).obj (op n)

private abbrev affinePointEval (A : CommAlgCat.{u} R) :
    CommGroupScheme (Spec R) ⥤ AddCommGrpCat.{u} :=
  additivePointFunctor (Spec R) ⋙ (evaluation _ _).obj (op (affineTest A))

/-- The kernel of multiplication by `p` at level `n + 1` is exactly level one
on every affine test, by the actual inclusion. -/
def finiteLevelPrimeKernelEquiv (A : CommAlgCat.{u} R) (n : ℕ) :
    G.affineLevelPoints A 1 ≃+
      (nsmulAddMonoidHom (α := G.affineLevelPoints A (n + 1)) p).ker := by
  let E := affinePointEval A
  let i : n ⟶ n + 1 := homOfLE (Nat.le_add_right n 1)
  let j : 1 ⟶ n + 1 := homOfLE (Nat.le_add_left 1 n)
  let q := E.map (G.transfer i)
  let f := E.map (G.inclusions.map j)
  let h := E.map (G.inclusions.map i)
  have hh : Function.Injective h := by
    intro x y he
    exact congrArg Additive.ofMul (G.inclusion_affine_injective i A (congrArg Additive.toMul he))
  have hf : Function.Injective f := by
    intro x y he
    exact congrArg Additive.ofMul (G.inclusion_affine_injective j A (congrArg Additive.toMul he))
  have hmul : q ≫ h = p • 𝟙 (E.obj (G.inclusions.obj (n + 1))) := by
    dsimp only [q, h]
    rw [← E.map_comp, G.multiplication, Nat.add_sub_cancel_left, pow_one,
      Functor.map_nsmul, E.map_id]
  have hzero (x : G.affineLevelPoints A (n + 1)) :
      p • x = 0 ↔ q x = 0 := by
    change _ ↔ q.hom x = 0
    have he : h (q x) = p • x := ConcreteCategory.congr_hom hmul x
    constructor
    · intro hz
      apply hh
      exact (he.trans hz).trans h.hom.map_zero.symm
    · intro hz
      exact he.symm.trans ((congrArg h.hom hz).trans h.hom.map_zero)
  have hexact (x : G.affineLevelPoints A (n + 1)) : q x = 0 ↔
      ∃ y : G.affineLevelPoints A 1, f y = x := by
    have hs := (G.shortExact n 1).2.1 A x.toMul
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := hs.mp (congrArg Additive.toMul hx)
      exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩
    · rintro ⟨v, hv⟩
      exact congrArg Additive.ofMul (hs.mpr ⟨v.toMul, congrArg Additive.toMul hv⟩)
  let e : G.affineLevelPoints A 1 →+
      (nsmulAddMonoidHom (α := G.affineLevelPoints A (n + 1)) p).ker :=
    f.hom.codRestrict _ fun x => (hzero (f x)).mpr ((hexact (f x)).mpr ⟨x, rfl⟩)
  refine AddEquiv.ofBijective e ⟨fun _ _ he => hf (congrArg Subtype.val he), ?_⟩
  intro x
  obtain ⟨y, hy⟩ := (hexact x.val).mp ((hzero x.val).mp x.property)
  exact ⟨y, Subtype.ext hy⟩

variable (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]

local notation "Aₖ" => CommAlgCat.of R K

/-- At a geometric test the finite level has the cardinality given by height,
provided the prime is a unit on the base. -/
theorem finiteLevel_geometric_card (hp : IsUnit (p : R)) {r : ℕ} (hr : G.HasHeight r)
    (n : ℕ) : Nat.card (G.affineLevelPoints Aₖ n) = p ^ (n * r) := by
  let X := (G.inclusions.obj n).X
  have : IsFinite X.hom := (G.finiteLocallyFree n).1
  have : Etale X.hom := G.finiteLevel_etale hp n
  let t : Spec (CommRingCat.of K) ⟶ Spec R := (affineTest Aₖ).hom
  let e : G.affineLevelPoints Aₖ n ≃ {z : Spec (CommRingCat.of K) ⟶ X.left // z ≫ X.hom = t} :=
    { toFun := fun z => ⟨z.toMul.left, Over.w z.toMul⟩
      invFun := fun z => Additive.ofMul (Over.homMk z.val z.property)
      left_inv := fun z => congrArg Additive.ofMul (Over.OverMorphism.ext rfl)
      right_inv := fun z => Subtype.ext rfl }
  let x : Spec (CommRingCat.of K) := Classical.arbitrary _
  exact (Nat.card_congr e).trans
    ((Langlands.AlgebraicGeometry.FiniteEtale.natCard_lifts_eq_finrank X.hom t x).trans
      ((G.finiteLevel_finrank_eq_levelRank n (t x)).trans (hr n (t x))))

/-- Positive finite levels of a height-`r` p-divisible group on geometric tests
are free residue modules of rank `r` when the prime is invertible. -/
def finiteLevelGeometricBasis (hp : IsUnit (p : R)) {r : ℕ} (hr : G.HasHeight r) (n : ℕ) :
    letI := G.schematicTateLevelResidueModule (affineTest Aₖ) (op (n + 1))
    (Fin r → ZMod (p ^ (n + 1))) ≃ₗ[ZMod (p ^ (n + 1))] G.affineLevelPoints Aₖ (n + 1) := by
  letI := G.schematicTateLevelResidueModule (affineTest Aₖ) (op (n + 1))
  have hcard := G.finiteLevel_geometric_card K hp hr (n + 1)
  have hfin : Finite (G.affineLevelPoints Aₖ (n + 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hpCard : Nat.card (nsmulAddMonoidHom (α := G.affineLevelPoints Aₖ (n + 1)) p).ker =
      p ^ r := (Nat.card_congr (G.finiteLevelPrimeKernelEquiv Aₖ n).symm.toEquiv).trans
        (by simpa only [one_mul] using G.finiteLevel_geometric_card K hp hr 1)
  let e := Langlands.AbelianScheme.Tate.piZmodEquivOfPrimePowerCard
    (G.affineLevelPoints Aₖ (n + 1)) p (n + 1) r Fact.out
    (schematicTateLevel_nsmul (G := G) (affineTest Aₖ) (n + 1))
    (by rwa [← pow_mul]) hpCard
  exact { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }

end Langlands.PDivisibleGroup
