import Langlands.GroupScheme.Torus.CocharacterBaseChange
import Langlands.GroupScheme.Torus.WeilCocharacterDetection
import Langlands.GroupScheme.Torus.NoClosedTorus
import Mathlib.FieldTheory.Galois.GaloisClosure

/-! # Finite-Galois fields of definition of actual cocharacters -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    {Λ : Type u} [AddCommGroup Λ]
    [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom]

/-- The exact multiplicative point over a Galois extension has a finite-Galois
field of definition. -/
theorem IsMult.exists_finiteGalois_coeffMap_eq
    {F L : Type u} [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    [IsGalois F L]
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsMult x) :
    ∃ N : FiniteGaloisIntermediateField F L,
      ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ),
        IsMult y ∧ coeffMap (N.toIntermediateField.val.restrictScalars k) y = x := by
  obtain ⟨E, hE, y, hy, hyx⟩ := hx.exists_finiteDimensional_coeffMap_eq (F := F)
  let := hE
  let N : FiniteGaloisIntermediateField F L :=
    { IntermediateField.normalClosure F E L with
      finiteDimensional := _root_.normalClosure.is_finiteDimensional F E L
      isGalois := IsGalois.normalClosure F E L }
  let i : E →ₐ[k] N :=
    (IntermediateField.inclusion (IntermediateField.le_normalClosure E)).restrictScalars k
  refine ⟨N, coeffMap i y, hy.coeff_map i, ?_⟩
  rw [coeffMap_comp]
  exact hyx

section ActualHom

variable (K : Type u) [Field K] [Algebra k K]

local notation "Z_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) Z

local instance finiteGaloisDescentTargetAffine : IsAffine (Z_K).toGrp.X.left := by
  change IsAffine (CategoryTheory.Limits.pullback Z.toGrp.X.hom (algebraBaseMap k K))
  infer_instance

omit [LocallyOfFiniteType Z.toGrp.X.hom] in
/-- Actual homomorphisms into the pullback are the original multiplicative
points with extension-field coefficients. -/
def baseChangedHomEquivMultiplicativePoints :
    ((Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp ⟶ (Z_K).toGrp) ≃
      multiplicativePoints Z K Λ :=
  (homEquivMultiplicativePoints (Z := Z_K) (Λ := Λ)).trans
    (multiplicativeBaseChangeEquiv (Z := Z) (Λ := Λ) K).toEquiv

omit [LocallyOfFiniteType Z.toGrp.X.hom] in
@[simp]
theorem baseChangedHomEquivMultiplicativePoints_zero :
    baseChangedHomEquivMultiplicativePoints (Z := Z) (Λ := Λ) K 0 = 1 := by
  simp [baseChangedHomEquivMultiplicativePoints]

omit [LocallyOfFiniteType Z.toGrp.X.hom] in
/-- A one-dimensional diagonalizable presentation identifies actual
cocharacters with multiplicative universal points over the extension. -/
def gmHomEquivMultiplicativePoints :
    ((Gm (Spec (CommRingCat.of K))).toGrp ⟶ (Z_K).toGrp) ≃
      multiplicativePoints Z K (PUnit.{u+1} → ℤ) :=
  let eK : (Gm (Spec (CommRingCat.of K))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of K)
        (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  (eK.homCongr (Iso.refl (Z_K).toGrp)).trans
    (baseChangedHomEquivMultiplicativePoints (Z := Z) K)

omit [LocallyOfFiniteType Z.toGrp.X.hom] in
@[simp]
theorem gmHomEquivMultiplicativePoints_zero :
    gmHomEquivMultiplicativePoints (Z := Z) K 0 = 1 := by
  simp [gmHomEquivMultiplicativePoints]

end ActualHom

section Vanishing

variable
    (hZ : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range f = ⊥)

include hZ

omit [LocallyOfFiniteType Z.toGrp.X.hom] in
/-- Vanishing of maps from base-field tori kills cocharacters over every
finite Galois extension by the actual Weil transfer. -/
theorem gm_hom_eq_zero_of_finiteGalois
    (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z).toGrp) : nu = 0 := by
  apply WeilGm.cocharacter_eq_zero_of_transfer_eq_zero k K Z nu
  exact SubgroupFunctor.eq_zero_of_range_eq_bot
    (hZ (WeilGm.commGroupScheme (CommRingCat.of k) K)
      (WeilGm.isTorus_of_finite_separable k K) (WeilGm.cocharacterTransfer k K Z nu))

/-- Vanishing of base-field torus maps forces every multiplicative universal
point over an arbitrary Galois extension to be the identity. -/
theorem multiplicativePoint_eq_one_of_isGalois
    (L : Type u) [Field L] [Algebra k L] [IsGalois k L]
    (x : multiplicativePoints Z L (PUnit.{u+1} → ℤ)) : x = 1 := by
  obtain ⟨N, y, hy, hyx⟩ := x.property.exists_finiteGalois_coeffMap_eq (F := k)
  have hyone : (⟨y, hy⟩ : multiplicativePoints Z N (PUnit.{u+1} → ℤ)) = 1 := by
    let e := gmHomEquivMultiplicativePoints (Z := Z) N
    have he := gm_hom_eq_zero_of_finiteGalois hZ N (e.symm ⟨y, hy⟩)
    have h := congrArg e he
    rw [Equiv.apply_symm_apply] at h
    exact h.trans (gmHomEquivMultiplicativePoints_zero (Z := Z) N)
  apply Subtype.ext
  rw [← hyx, show y = 1 from congrArg Subtype.val hyone, map_one]
  rfl

/-- Vanishing of maps from tori is sufficient to kill all actual cocharacters
after an arbitrary Galois field extension. -/
theorem gm_hom_eq_zero_of_isGalois
    (L : Type u) [Field L] [Algebra k L] [IsGalois k L]
    (nu : (Gm (Spec (CommRingCat.of L))).toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj Z).toGrp) : nu = 0 := by
  apply (gmHomEquivMultiplicativePoints (Z := Z) L).injective
  rw [gmHomEquivMultiplicativePoints_zero]
  exact multiplicativePoint_eq_one_of_isGalois hZ L _

end Vanishing

end Langlands.GroupScheme.CocharacterDatum
