/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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

/-! # Vocabulary for completed scalar tensor models under a scheme isomorphism

The index n means positive exponent n+1. Inverse image is the recorded sectionwise
model, with its action transported by the completed or finite structure map.
Scalar tensors use the existing sheafified tensor, with scalar written first.

## References

* Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4)
* Stacks 03D6
* Stacks 03D2
* Stacks 03EK, 03EL and 06YY
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

/-- The existing ordinary extension at a finite level, supplied with its universal
counit. Its objects and maps are fixed by the sheafified balanced tensor. -/
def finiteChangeData (W : Scheme.{t}) (n : ℕ) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (integralScalarQuotientSheafMap l E L ι W n))

/-- Ordinary extension from E's finite coefficient ring to L's, with the same index. -/
abbrev finiteExtension (W : Scheme.{t}) (n : ℕ) :=
  (finiteChangeData l E L ι W n).E

/-- The actual balanced pure tensor in finite extension, including the witness's
object identification. -/
def finitePure (W : Scheme.{t}) (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U) :
    ((finiteExtension l E L ι W n).obj M).val.obj U :=
  (eqToHom ((finiteChangeData l E L ι W n).obj_eq M).symm).val.app U
    ((toSheafify (ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarQuotientSheafMap l E L ι W n) M).presheaf).app U
      (s ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U,
        ((integralScalarQuotientSheafMap l E L ι W n).hom.app U).hom] x))

/-- Completed-coefficient inverse image on complexes. -/
abbrev inverseComplex :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Z as a functor of P. -/
abbrev leftComplex :=
  inverseComplex l E g ⋙ completedOrdinaryScalarComplex l E L ι X

/-- G_L Q as a functor of P. -/
abbrev rightComplex :=
  completedOrdinaryScalarComplex l E L ι Y ⋙ inverseComplex l L g

/-- The lower left: reduce over E, transport its finite action, then extend to L. -/
abbrev finiteLeft (n : ℕ) :=
  unrestrictedIntegralFiniteComplex l E Y n ⋙
    (inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ) ⋙
      (finiteExtension l E L ι X n).mapHomologicalComplex (.up ℤ)

/-- The lower right: extend directly to L's finite coefficients, then inverse image. -/
abbrev finiteRight (n : ℕ) :=
  integralScalarFiniteComplex l E L ι Y n ⋙
    (inverseImageFiniteModules l L g n).mapHomologicalComplex (.up ℤ)

/-- Lower-left complex with its completed L action, for quotient and transition maps. -/
abbrev restrictedLeft (n : ℕ) :=
  finiteLeft l E L ι g n ⋙ integralOperationsRestrict l L X n

/-- Lower-right complex with its completed L action, for quotient and transition maps. -/
abbrev restrictedRight (n : ℕ) :=
  finiteRight l E L ι g n ⋙ integralOperationsRestrict l L X n

/-- A double tensor in the lower-left complex, in the canonical sectionwise model. -/
def doublePure (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (U : X.ProEt)
    (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((restrictedLeft l E L ι g n).obj P).X i).val.obj (op U) :=
  finitePure l E L ι X n
    ((inverseImageFiniteModules l E g n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj (P.X i))) (op U) s
    (unrestrictedIntegralTensorSection l E Y n (P.X i)
      (op ((proEtaleIsoPostcompose g).obj U)) a x)

attribute [local irreducible] completedScalarChangeData completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  integralScalarReductionWitness integralScalarReduction integralScalarTensorSection
  unrestrictedIntegralReductionExistence unrestrictedIntegralReductionFunctor
  unrestrictedIntegralTensorSection inverseImageCompletedCoefficientMap finiteChangeData
  finitePure doublePure

/-- K-flatness and flat terms for inverse image, Q and Z. -/
def PreservesModels : Prop :=
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      integralOperationsGoodComplex l E X ((inverseComplex l E g).obj P.obj) ∧
      integralOperationsGoodComplex l L Y
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) ∧
      integralOperationsGoodComplex l L X ((leftComplex l E L ι g).obj P.obj)

/-- The local formula for the completed tensor isomorphism. -/
def CompletedFormula
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g) : Prop :=
    ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((b.hom.app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s) x) =
        completedScalarTensorSection l E L ι Y (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x

/-- The finite comparison on double pure tensors. -/
def FiniteFormula
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
      (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app (op U)
        (doublePure l E L ι g n P.obj i U s a x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) *
          (integralScalarQuotientSheafMap l E L ι Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) a) x

/-- The canonical quotient from Z on pure tensors. -/
def LeftQuotientFormula
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((vleft n).app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s) x) =
      doublePure l E L ι g n P.obj i U
        ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s)) 1 x

/-- The inverse image of the coefficient quotient from Q. -/
def RightQuotientFormula
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((vright n).app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι Y (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) x

/-- The specified completed-to-finite square. -/
def QuotientSquare
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
      b.hom.app P ≫ (vright n).app P =
        (vleft n).app P ≫ (integralOperationsRestrict l L X n).map ((bfin n).hom.app P)

/-- The quotient transition on the two scalar factors on the left. -/
def LeftTransitionFormula
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X (n + 1)).obj.obj (op U))
      (a : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((tleft n).app P).f i).val.app (op U)
        (doublePure l E L ι g (n + 1) P.obj i U s a x) =
      doublePure l E L ι g n P.obj i U
        ((integralCoefficientSheafTransition l L X n).hom.app (op U) s)
        ((integralCoefficientSheafTransition l E Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) a) x

/-- The quotient transition on the final scalar factor on the right. -/
def RightTransitionFormula
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((tright n).app P).f i).val.app (op U)
        (integralScalarTensorSection l E L ι Y (n + 1) (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((integralCoefficientSheafTransition l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) x

/-- The specified finite comparison commutes with quotient transitions. -/
def TransitionSquare
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
      (integralOperationsRestrict l L X (n + 1)).map ((bfin (n + 1)).hom.app P) ≫
          (tright n).app P =
        (tleft n).app P ≫ (integralOperationsRestrict l L X n).map ((bfin n).hom.app P)

/-- Canonical K-flat computations and descent of the same chain comparison. -/
def DerivedModel
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (β : inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
        completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g) : Prop :=
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (completedScalarCounit l E L ι Y P.obj) ∧
      IsIso (completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj)) ∧
      β.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (inverseImageIntegralDerived l L g).map (completedScalarCounit l E L ι Y P.obj) ≫
          (inverseImageIntegralModules l L g).mapDerivedCategoryFactors.hom.app
            ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) =
        (completedDerivedScalarExtension l E L ι X).map
            ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
          completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj) ≫
          DerivedCategory.Q.map (b.hom.app P)

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
