/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonRepresentative
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Completed.CompletedLineComplete

/-! # Derived reductions and completeness of a completed line

Source: coefficient-twist blueprint, proof steps 9 and 11.
(blueprint: lem-pur-completed-line-derived)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

private noncomputable def extensionPresheafIso
    (S : Scheme.{u})
    {R R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (a : R ⟶ R') (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M ≅
      SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} a M := by
  letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S
  exact PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x =>
      change SheafOfModules.changeOfRingsMap a M i
          (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) =
        SheafOfModules.changeOfRingsMapOfUniverses a M i
          (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)
      exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap a M i) s x).trans
        (SheafOfModules.changeOfRingsMap_tmulOfUniverses a M i s x).symm)

/-- A line over the completed coefficient sheaf has underived finite reductions
and is complete for the actual augmented derived-reduction tower.

Source: coefficient-twist blueprint, proof steps 9 and 11; Bhatt--Scholze,
Section 6.5; Stacks Project, Tags 06YS, 06YY and 03CO.
(blueprint: lem-pur-completed-line-derived)

Proof: restriction to a site slice is exact. On a trivializing cover tensor by
the line is tensor by the unit and therefore exact, so the degree-zero complex
of the line is K-flat. The canonical K-flat counit computes each derived reduction
as the degree-zero complex of the ordinary scalar reduction. These identifications
commute with the quotient transitions and the augmentation, because they use the
counit and the actual coefficient projections. After restriction to this same
cover the ordinary quotient tower is the coefficient quotient tower, whose limit
is the completed coefficient sheaf; its transitions are locally surjective.
Both limit identification and epimorphy descend from the cover. Apply the
surjective-tower derived-limit theorem to the ordinary reduction tower. Its Roos
triangle, with the actual augmentation, is exactly the recorded derived-complete
predicate. The argument is independent of a global finite-field datum, and also
applies on an empty scheme, where all these module sheaves are zero. -/
theorem completedLine_derived (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E S))
    (hL : L.IsFiniteLocallyFreeOfRank 1)
    (D : WeilConjectures.FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S
    (∀ n : ℕ, Nonempty
      ((WeilConjectures.integralDerivedReduction.{d, u, u} l E S D hl n).obj
          ((DerivedCategory.singleFunctor _ 0).obj L) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
            (WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E S n) L))) ∧
    WeilConjectures.IsDerivedComplete.{d, u, u} l E S D hl
      ((DerivedCategory.singleFunctor _ 0).obj L) := by
  classical
  let := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E S
  let C : CochainComplex (SheafOfModules.{u + 1}
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E S)) ℤ :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L
  have ex := @CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
    S.ProEt inferInstance (essentiallySmallSelf.{0} S.ProEt) (ProEt.topology S)
    inferInstance inferInstance inferInstance R C
  obtain ⟨P, f, hP, hflat, _, _⟩ := ex
  have hs : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology S)
      (R := R) (P.X i) := fun i ↦
    (exactFunctor _ _).prop_of_iso
      (@SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        S.ProEt inferInstance (essentiallySmallSelf.{0} S.ProEt)
        (ProEt.topology S) R (P.X i)).symm (hflat i)
  let PG : (WeilConjectures.IntegralOnSlice.Good.{u, u} l E S none).FullSubcategory :=
    ⟨P, hP, hs⟩
  let := hL
  obtain ⟨hC, _, _⟩ := WeilConjectures.integralLineTensorComparison_representative.{u, u} l E S L PG
  constructor
  · intro n
    let := WeilConjectures.integralReductionChangeOfRingsAdditive l E S D hl n
    let F := WeilConjectures.integralReductionChangeOfRings l E S D hl n
    let a := WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n
    let e : F.obj L ≅ SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a L :=
      eqToIso ((WeilConjectures.integralReductionExistence l E S D hl n).choose_spec.choose L) ≪≫
        (PresheafOfModules.sheafification (𝟙 _)).mapIso (extensionPresheafIso S a L)
    refine ⟨(WeilConjectures.integralDerivedReductionKFlatIso l E S D hl n C hC) ≪≫ ?_⟩
    exact DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app L) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e
  · exact completedLine_complete S l E L hL D hl

end AlgebraicGeometry.Scheme
