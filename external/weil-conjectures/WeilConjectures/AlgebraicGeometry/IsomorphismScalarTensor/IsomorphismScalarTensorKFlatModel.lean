/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteModel
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.IsomorphismScalarKFlatDescent.IsomorphismScalarKFlatDescent

/-! # Coefficient-compatible K-flat tensor models under a scheme isomorphism

The index n means positive exponent n+1. Inverse image is the recorded sectionwise
model, with its action transported by the completed or finite structure map.
Scalar tensors use the existing sheafified tensor, with scalar written first.

## References

* Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4)
* Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4) for completed pullback
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

section DerivedDescent
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard completedCoefficientMap

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def completed_counit (W : Scheme.{t}) :
    DerivedCategory.Q ⋙ completedDerivedScalarExtension l E L ι W ⟶
      completedOrdinaryScalarComplex l E L ι W ⋙ DerivedCategory.Q :=
  homotopyCounitOnComplex (completedOrdinaryScalarExtension l E L ι W)
    (completedDerivedScalarExtension l E L ι W)
    ((completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose)

private theorem completed_counit_app (W : Scheme.{t})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (completed_counit l E L ι W).app P = completedScalarCounit l E L ι W P := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem completed_counit_computes (W : Scheme.{t})
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    IsIso (completedScalarCounit l E L ι W P) := by
  rw [← completedScalarCochainModel_counit l E L ι W]
  exact (completedScalarCochainModel l E L ι W).computes P hP

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem descend_model
    (h : PreservesModels l E L ι g)
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g) :
    ∃ β : inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
      completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g,
      DerivedModel l E L ι g b β := by
  classical
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} X
  let : (ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let : (inverseImageIntegralModules l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive g (inverseImageCompletedCoefficientMap l E g)
  let : (inverseImageIntegralModules l L g).Additive :=
    isoSectionwiseModuleInverseImage_additive g (inverseImageCompletedCoefficientMap l L g)
  let : PreservesFiniteLimits (inverseImageIntegralModules l E g) :=
    isoSectionwiseModuleInverseImage_limits g
      (inverseImageCompletedCoefficientMap l E g)
  let : PreservesFiniteColimits (inverseImageIntegralModules l E g) :=
    isoSectionwiseModuleInverseImage_colimits g
      (inverseImageCompletedCoefficientMap l E g)
  let : PreservesFiniteLimits (inverseImageIntegralModules l L g) :=
    isoSectionwiseModuleInverseImage_limits g
      (inverseImageCompletedCoefficientMap l L g)
  let : PreservesFiniteColimits (inverseImageIntegralModules l L g) :=
    isoSectionwiseModuleInverseImage_colimits g
      (inverseImageCompletedCoefficientMap l L g)
  let p := integralOperationsGoodComplex l E Y
  let F := inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X
  let G := completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g
  let U := leftComplex l E L ι g ⋙ DerivedCategory.Q
  let V := rightComplex l E L ι g ⋙ DerivedCategory.Q
  let a : DerivedCategory.Q ⋙ F ⟶ U :=
    AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.composeSquare
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      (inverseComplex l E g) (completedOrdinaryScalarComplex l E L ι X)
      (inverseImageIntegralDerived l E g) (completedDerivedScalarExtension l E L ι X)
      (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom (completed_counit l E L ι X)
  let d : DerivedCategory.Q ⋙ G ⟶ V :=
    AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.composeSquare
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      (completedOrdinaryScalarComplex l E L ι Y) (inverseComplex l L g)
      (completedDerivedScalarExtension l E L ι Y) (inverseImageIntegralDerived l L g)
      (completed_counit l E L ι Y) (inverseImageIntegralModules l L g).mapDerivedCategoryFactors.hom
  have hCY (P : p.FullSubcategory) :
      IsIso (completedScalarCounit l E L ι Y P.obj) :=
    completed_counit_computes l E L ι Y P.obj P.property.1
  have hCX (P : p.FullSubcategory) :
      IsIso (completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj)) :=
    completed_counit_computes l E L ι X ((inverseComplex l E g).obj P.obj) (h P).1.1
  have ha (P : p.FullSubcategory) : IsIso (a.app P.obj) := by
    have := hCX P
    change IsIso ((completedDerivedScalarExtension l E L ι X).map
      ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
        completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj))
    infer_instance
  have hd (P : p.FullSubcategory) : IsIso (d.app P.obj) := by
    have := hCY P
    change IsIso ((inverseImageIntegralDerived l L g).map
      (completedScalarCounit l E L ι Y P.obj) ≫
      (inverseImageIntegralModules l L g).mapDerivedCategoryFactors.hom.app
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj))
    infer_instance
  have hres (K : CochainComplex (integralTowerModules l E Y) ℤ) :
      ∃ (P : CochainComplex (integralTowerModules l E Y) ℤ) (s : P ⟶ K),
        QuasiIso s ∧ p P := by
    obtain ⟨P, s, hP, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E Y) K
    refine ⟨P, s, hs, hP, fun n ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.X n)).symm (hf n)
  obtain ⟨β, hβ, _⟩ :=
    AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.descend_normalized
      p hres F G U V a d ha hd (Functor.isoWhiskerRight b DerivedCategory.Q)
  refine ⟨β, fun P ↦ ⟨hCY P, hCX P, ?_⟩⟩
  have he := hβ P.obj P.obj (𝟙 P.obj) inferInstance P.property
  have he' :=
    AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.normalized_id
      DerivedCategory.Q F G U V a d β P.obj
      (DerivedCategory.Q.map (b.hom.app P)) he
  dsimp only [a, d,
    AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.composeSquare] at he'
  simpa only [completed_counit_app, Category.assoc] using he'

end DerivedDescent

/-- The completed and finite tensor comparisons, their quotient/transition squares,
and their normalized descent to the ordinary unbounded derived categories. -/
theorem isomorphism_scalar_tensor_kflat_model
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
      (β : inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
        completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g)
      (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
      (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
      (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n),
    PreservesModels l E L ι g ∧
    CompletedFormula l E L ι g b ∧
    FiniteFormula l E L ι g bfin ∧
    LeftQuotientFormula l E L ι g vleft ∧
    RightQuotientFormula l E L ι g vright ∧
    QuotientSquare l E L ι g b bfin vleft vright ∧
    LeftTransitionFormula l E L ι g tleft ∧
    RightTransitionFormula l E L ι g tright ∧
    TransitionSquare l E L ι g bfin tleft tright ∧
    DerivedModel l E L ι g b β  := by
  obtain ⟨b, hp, hb⟩ := scalar_completed_model l E L ι g _hX _hY
  obtain ⟨bfin, vleft, vright, tleft, tright, hf, hvl, hvr, hq, htl, htr, ht⟩ :=
    scalar_finite_model l E L ι g b hb
  obtain ⟨β, hβ⟩ := descend_model l E L ι g hp b
  exact ⟨b, β, bfin, vleft, vright, tleft, tright,
    hp, hb, hf, hvl, hvr, hq, htl, htr, ht, hβ⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
