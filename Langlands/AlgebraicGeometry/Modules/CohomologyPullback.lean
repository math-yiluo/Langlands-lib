import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackSections
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.Cohomology.AcyclicTermsDerivedUnitProof
import Langlands.Cohomology.DerivedPlus

/-!
# Canonical pullback on the cohomology of actual scheme modules
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- The actual pullback adjunction unit followed by the pushforward of the
augmentation into the chosen injective resolution of the pulled-back module. -/
def pullbackResolutionAugmentation (h : Y ⟶ X) (M : X.left.Modules) :
    (CochainComplex.singleFunctor X.left.Modules 0).obj M ⟶
      ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj
        (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).cochainComplex :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ X.left.Modules).map
          ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
        AcyclicResolution.mapAugmentation (Scheme.Modules.pushforward h.left)
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)))
      ComplexShape.embeddingUpNat ≫
    (DerivedPlus.mapExtendIso (Scheme.Modules.pushforward h.left)
      (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).cocomplex
      ComplexShape.embeddingUpNat).hom

/-- The augmentation as a map in the bounded below derived category. -/
def pullbackDerivedAugmentation (h : Y ⟶ X) (M : X.left.Modules) :
    (DerivedCategory.Plus.singleFunctor X.left.Modules 0).obj M ⟶
      DerivedCategory.Plus.Q.obj
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)))) :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).hom.app M ≫
      (DerivedCategory.singleFunctorIsoCompQ X.left.Modules 0).hom.app M ≫
      DerivedCategory.Q.map (pullbackResolutionAugmentation h M) ≫
      (DerivedCategory.Plus.QCompιIso X.left.Modules).inv.app
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)))))

/-- Pushforward and sections identify the termwise section complexes of
any bounded below complex on the source scheme. -/
def pullbackSectionsComplexIso (h : Y ⟶ X) (K : CochainComplex.Plus Y.left.Modules) :
    (relativeGlobalSections X.hom).mapCochainComplexPlus.obj
        ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K) ≅
      (relativeGlobalSections Y.hom).mapCochainComplexPlus.obj K :=
  (CochainComplex.Plus.ι (ModuleCat.{u} R)).preimageIso
    ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h) _).app K.obj)

/-- The canonical derived pullback map, computed on an injective resolution
of the actual pulled-back module. -/
def relativeDerivedSectionsPullback (h : Y ⟶ X) (M : X.left.Modules) :
    (DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).obj M ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections Y.hom)).obj
        ((Scheme.Modules.pullback h.left).obj M) := by
  let I := injectiveResolution ((Scheme.Modules.pullback h.left).obj M)
  let K := DerivedPlus.resolutionPlus I
  let L := (Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K
  have hL (i : ℤ) (q : ℕ) :
      IsZero (((relativeGlobalSections X.hom).rightDerived (q + 1)).obj (L.obj.X i)) :=
    (pushforwardInjectiveAcyclic Y.left X.left h.left (K.obj.X i)
      inferInstance q).2 R X.hom
  haveI := acyclicTermsDerivedUnitStatement X.left.Modules (ModuleCat.{u} R)
    (relativeGlobalSections X.hom) L hL
  exact (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
      (pullbackDerivedAugmentation h M) ≫
    inv ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app L) ≫
    DerivedCategory.Plus.Q.map (pullbackSectionsComplexIso h K).hom ≫
    (DerivedPlus.derivedComplexIso (relativeGlobalSections Y.hom) I).inv

/-- Canonical pullback on the actual published right-derived relative
sections functors, in every natural degree. -/
def relativeCohomologyPullback (h : Y ⟶ X) (M : X.left.Modules) (n : ℕ) :
    (relativeCohomology X.hom n).obj M ⟶
      (relativeCohomology Y.hom n).obj
        ((Scheme.Modules.pullback h.left).obj M) :=
  (DerivedPlus.homologyIso (relativeGlobalSections X.hom) (injectiveResolution M) n).inv ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
      (relativeDerivedSectionsPullback h M) ≫
    (DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
      (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)) n).hom

end Langlands.AlgebraicGeometry.Modules.DerivedSections
