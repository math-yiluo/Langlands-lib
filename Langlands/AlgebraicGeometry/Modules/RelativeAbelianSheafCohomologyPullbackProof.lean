import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomPullbackExt
import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyPullbackStatement

/-! # Relative cohomology and arbitrary pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic DerivedSectionsHomComparison DerivedSections
open AbelianSheafCohomologyPullback AbelianSheafDerivedSections

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048
set_option autoImplicit false

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

lemma relativeComparisonOnComplex_pushforward_single (f : Y ⟶ X)
    (N : Y.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj
      ((Scheme.Modules.pushforward f.left).obj N)) n) :
    (comparisonOnComplex.{u+1} (relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
      (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom) (n : ℤ)).app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj
          ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj N))
        ((derivedSections.{u+1} (relativeGlobalSections X.hom)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).map
          (DerivedCategory.Plus.Q.map
            ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward f.left)).hom.app N))
          ((derivedSections.{u+1} (relativeGlobalSections X.hom)
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).map
            ((DerivedPlus.singlePlusQIso X.left.Modules).hom.app
              ((Scheme.Modules.pushforward f.left).obj N))
            (relativeSingleDerivedSectionsClass ((Scheme.Modules.pushforward f.left).obj N) n x))) =
      x.hom ≫ (relativePushforwardSingleDerivedIso f N).inv⟦(n : ℤ)⟧' := by
  let C := comparisonOnComplex.{u+1} (relativeGlobalSections X.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
    (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom) (n : ℤ)
  let D := derivedSections.{u+1} (relativeGlobalSections X.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)
  let a := (DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward f.left)).hom.app N
  let y := D.map ((DerivedPlus.singlePlusQIso X.left.Modules).hom.app
    ((Scheme.Modules.pushforward f.left).obj N))
      (relativeSingleDerivedSectionsClass ((Scheme.Modules.pushforward f.left).obj N) n x)
  have h := ConcreteCategory.congr_hom (C.naturality a) y
  change C.app _ (D.map (DerivedCategory.Plus.Q.map a) y) =
    C.app _ y ≫ (DerivedCategory.Q.map
      (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).map a.hom))⟦(n : ℤ)⟧' at h
  change C.app _ (D.map (DerivedCategory.Plus.Q.map a) y) = _
  rw [h]
  change (C.app _ y ≫ _) = _
  rw [relativeComparisonOnComplex_singlePlus]
  change (x.hom ≫
    (shiftFunctor (DerivedCategory.{u+1} (TopCat.Sheaf AddCommGrpCat.{u} X.left.toTopCat))
      (n : ℤ)).map ((singleComplexDerivedIso.{u+1} (toAbSheaf X.left)
        ((Scheme.Modules.pushforward f.left).obj N)).inv)) ≫
    (shiftFunctor (DerivedCategory.{u+1} (TopCat.Sheaf AddCommGrpCat.{u} X.left.toTopCat))
      (n : ℤ)).map (DerivedCategory.Q.map
        (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).map a.hom)) = _
  rw [Category.assoc, ← Functor.map_comp, relativePushforwardSingleDerivedIso_inv]
  rfl

lemma relativeDerivedComplexSectionsPullback_single_fac (f : Y ⟶ X)
    (N : Y.left.Modules) (n : ℤ) :
    (sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).map
        ((pushforwardSingleDerivedSectionsComparison f).app N) ≫
      (derivedSections.{u+1} (relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).map
          ((DerivedPlus.singlePlusQIso Y.left.Modules).hom.app N) =
    (derivedSections.{u+1} (relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).map
        ((DerivedPlus.singlePlusQIso X.left.Modules).hom.app
          ((Scheme.Modules.pushforward f.left).obj N)) ≫
      (derivedSections.{u+1} (relativeGlobalSections X.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n).map
          (DerivedCategory.Plus.Q.map
            ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward f.left)).hom.app N)) ≫
      (relativeDerivedComplexSectionsPullback f n).app
        ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj N) := by
  let H := sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp, ← H.map_comp]
  congr 1
  simp only [pushforwardSingleDerivedSectionsComparison, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.comp_map, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

lemma relativeSingleDerivedSectionsClass_pushforward (f : Y ⟶ X)
    (N : Y.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj
      ((Scheme.Modules.pushforward f.left).obj N)) n) :
    (sectionsCohomology.{u+1} (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).map
      ((pushforwardSingleDerivedSectionsComparison f).app N)
      (relativeSingleDerivedSectionsClass ((Scheme.Modules.pushforward f.left).obj N) n x) =
    relativeSingleDerivedSectionsClass N n
      (pushforwardMap f.left.base
        (𝟙 ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N))) n x) := by
  let DY := derivedSections.{u+1} (relativeGlobalSections Y.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)
  let K := (DerivedPlus.singlePlusFunctor Y.left.Modules).obj N
  let CY := comparisonOnComplex.{u+1} (relativeGlobalSections Y.hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
    (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) (n : ℤ)
  have : IsIso (CY.app K) := by
    dsimp only [CY, comparisonOnComplex, NatTrans.comp_app, whiskerLeft_app]
    change IsIso ((relativeDerivedHomComparison Y.hom (n : ℤ)).app _ ≫ _)
    infer_instance
  let E := DY.map ((DerivedPlus.singlePlusQIso Y.left.Modules).hom.app N) ≫ CY.app K
  apply (asIso E).addCommGroupIsoToAddEquiv.injective
  change CY.app K (DY.map ((DerivedPlus.singlePlusQIso Y.left.Modules).hom.app N) _) =
    CY.app K (DY.map ((DerivedPlus.singlePlusQIso Y.left.Modules).hom.app N) _)
  have hfac := ConcreteCategory.congr_hom
    (relativeDerivedComplexSectionsPullback_single_fac f N (n : ℤ))
    (relativeSingleDerivedSectionsClass ((Scheme.Modules.pushforward f.left).obj N) n x)
  simp only [ConcreteCategory.comp_apply] at hfac
  erw [hfac]
  have hsquare := ConcreteCategory.congr_hom
    (NatTrans.congr_app (relativeComparisonOnComplex_pullback f (n : ℤ)) K)
    ((derivedSections.{u+1} (relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).map
      (DerivedCategory.Plus.Q.map
        ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward f.left)).hom.app N))
      ((derivedSections.{u+1} (relativeGlobalSections X.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n : ℤ)).map
        ((DerivedPlus.singlePlusQIso X.left.Modules).hom.app
          ((Scheme.Modules.pushforward f.left).obj N))
        (relativeSingleDerivedSectionsClass ((Scheme.Modules.pushforward f.left).obj N) n x)))
  simp only [NatTrans.comp_app, whiskerLeft_app, ConcreteCategory.comp_apply] at hsquare
  erw [← hsquare]
  dsimp only [K, CY, DY]
  erw [relativeComparisonOnComplex_pushforward_single f N n x,
    relativeComplexHomPullback_single f N n x, relativeComparisonOnComplex_singlePlus]

lemma relativeHAddEquiv_canonicalPushforward (f : Y ⟶ X)
    (N : Y.left.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X.left).obj
      ((Scheme.Modules.pushforward f.left).obj N)) n) :
    (canonicalPushforwardCohomologyMap f N n).hom
      (relativeHAddEquiv X.hom ((Scheme.Modules.pushforward f.left).obj N) n x) =
    relativeHAddEquiv Y.hom N n
      (pushforwardMap f.left.base
        (𝟙 ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj N))) n x) := by
  have h := congrArg (fun z =>
      (DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
        (injectiveResolution N) n).hom z.down)
    (relativeSingleDerivedSectionsClass_pushforward f N n x)
  change (DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
      (injectiveResolution N) n).hom
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((pushforwardSingleDerivedSectionsComparison f).app N)
        ((DerivedPlus.homologyIso (relativeGlobalSections X.hom)
          (injectiveResolution ((Scheme.Modules.pushforward f.left).obj N)) n).inv
          (relativeHAddEquiv X.hom ((Scheme.Modules.pushforward f.left).obj N) n x))) =
    (DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
      (injectiveResolution N) n).hom
      ((DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
        (injectiveResolution N) n).inv _) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h

/-- The actual relative additive comparison commutes with arbitrary pullback
and the prescribed coefficient adjunction. -/
theorem relativeAbelianSheafCohomologyPullback :
    RelativeAbelianSheafCohomologyPullbackStatement.{u} := by
  intro R X Y f M N k n x
  have hc := ConcreteCategory.congr_hom
    (relativeCohomologyPullback_coefficient f
      (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k) n)
    (relativeHAddEquiv X.hom M n x)
  simp only [ConcreteCategory.comp_apply, Equiv.apply_symm_apply] at hc
  rw [hc, relativeHAddEquiv_naturality, relativeHAddEquiv_canonicalPushforward]
  apply congrArg (relativeHAddEquiv Y.hom N n)
  unfold pushforwardMap
  rw [pullbackMap_naturality_left,
    ← (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      f.left.base).homEquiv_naturality_left_symm, Category.comp_id]

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
