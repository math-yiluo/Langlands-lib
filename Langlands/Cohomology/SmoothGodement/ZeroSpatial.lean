import Langlands.Cohomology.EquivariantGodementZeroMap
import Langlands.Cohomology.SmoothGodement.CoefficientInvariants

/-! # Degree-zero compatibility of proper smooth Godement spatial maps -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.SmoothGodementCohomology.Spatial

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [MulAction G Y]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The compact chain map preserves the actual augmentations, with original
proper compact pullback as its map of augmented sections. -/
@[reassoc]
theorem compactMap_augmentation (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothSheafCompactSections R G Y).map
        (Godement.smoothAugmentation R G Y ((SmoothDirectImage.functor f hf).obj F)) ≫
        (compactMap f hf hp F).f 0 =
      (ProperSmoothCompactSections.natTrans f hf hp).app F ≫
        (smoothSheafCompactSections R G X).map (Godement.smoothAugmentation R G X F) := by
  rw [compactMap_f, ← Functor.map_comp_assoc,
    Godement.SmoothSpatial.augmentation_complexMap]
  exact (ProperSmoothCompactSections.natTrans f hf hp).naturality
    (Godement.smoothAugmentation R G X F)

/-- The all-degree spatial map in degree zero is the original proper
compact-section pullback, under the existing canonical zero identifications. -/
@[reassoc]
theorem cohomologyMap_zero (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    cohomologyMap f hf hp F 0 ≫
        (smoothGodementCompactCohomologyZeroIso R G X).hom.app F =
      (smoothGodementCompactCohomologyZeroIso R G Y).hom.app
          ((SmoothDirectImage.functor f hf).obj F) ≫
        (ProperSmoothCompactSections.natTrans f hf hp).app F :=
  EquivariantGodementCohomology.homologyZeroIso_map
    (Godement.smoothZeroFunctor R G Y) (Godement.smoothCoaugmentation R G Y)
    (Godement.smoothZeroFunctor R G X) (Godement.smoothCoaugmentation R G X)
    (smoothSheafCompactSections R G Y) (smoothSheafCompactSections R G X)
    ((ProperSmoothCompactSections.natTrans f hf hp).app F)
    (compactMap f hf hp F) (compactMap_augmentation f hf hp F)

/-- Proper spatial pullback restricted to whole-group invariant compact sections. -/
def invariantSectionsNatTrans (hp : IsProperMap f) :
    SmoothDirectImage.functor (R := R) f hf ⋙
        SmoothSheafCohomology.invariantCompactSections R G Y ⟶
      SmoothSheafCohomology.invariantCompactSections R G X :=
  Functor.whiskerRight (ProperSmoothCompactSections.natTrans f hf hp)
    (smoothInvariants R G)

/-- Taking termwise invariants retains augmentation compatibility. -/
@[reassoc]
theorem invariantCompactMap_augmentation (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    (SmoothSheafCohomology.invariantCompactSections R G Y).map
        (Godement.smoothAugmentation R G Y ((SmoothDirectImage.functor f hf).obj F)) ≫
        (invariantCompactMap f hf hp F).f 0 =
      (invariantSectionsNatTrans f hf hp).app F ≫
        (SmoothSheafCohomology.invariantCompactSections R G X).map
          (Godement.smoothAugmentation R G X F) := by
  rw [invariantCompactMap_f]
  change (smoothInvariants R G).map
      ((smoothSheafCompactSections R G Y).map
        (Godement.smoothAugmentation R G Y ((SmoothDirectImage.functor f hf).obj F))) ≫
      (smoothInvariants R G).map ((compactMap f hf hp F).f 0) =
    (smoothInvariants R G).map ((ProperSmoothCompactSections.natTrans f hf hp).app F) ≫
      (smoothInvariants R G).map ((smoothSheafCompactSections R G X).map
        (Godement.smoothAugmentation R G X F))
  simpa only [Functor.map_comp] using
    congrArg (fun a => (smoothInvariants R G).map a) (compactMap_augmentation f hf hp F)

/-- Homology after invariant compact sections recovers the actual invariant
section map in degree zero; invariants need not be exact. -/
@[reassoc]
theorem invariantCohomologyMap_zero (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    invariantCohomologyMap f hf hp F 0 ≫
        (smoothGodementInvariantCompactCohomologyZeroIso R G X).hom.app F =
      (smoothGodementInvariantCompactCohomologyZeroIso R G Y).hom.app
          ((SmoothDirectImage.functor f hf).obj F) ≫
        (invariantSectionsNatTrans f hf hp).app F :=
  EquivariantGodementCohomology.homologyZeroIso_map
    (Godement.smoothZeroFunctor R G Y) (Godement.smoothCoaugmentation R G Y)
    (Godement.smoothZeroFunctor R G X) (Godement.smoothCoaugmentation R G X)
    (SmoothSheafCohomology.invariantCompactSections R G Y)
    (SmoothSheafCohomology.invariantCompactSections R G X)
    ((invariantSectionsNatTrans f hf hp).app F)
    (invariantCompactMap f hf hp F) (invariantCompactMap_augmentation f hf hp F)

/-- Resolve neither side: this is the actual full-coefficient section map. -/
def coefficientCompactSectionsNatTrans (hp : IsProperMap f) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙ smoothSheafCompactSections R G Y ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙ smoothSheafCompactSections R G X :=
  Functor.whiskerRight (SmoothDirectImage.coefficientNatTrans f hf)
      (smoothSheafCompactSections R G Y) ≫
    Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
      (ProperSmoothCompactSections.natTrans f hf hp)

/-- The actual full-coefficient section pullback, restricted to invariants. -/
def coefficientInvariantSectionsNatTrans (hp : IsProperMap f) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙
        SmoothSheafCohomology.invariantCompactSections R G Y ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙
        SmoothSheafCohomology.invariantCompactSections R G X :=
  Functor.whiskerRight (coefficientCompactSectionsNatTrans f hf hp) (smoothInvariants R G)

/-- The full-coefficient all-degree map commutes with the canonical
degree-zero compact-section identifications. -/
@[reassoc]
theorem coefficientCohomologyNatTrans_zero (hp : IsProperMap f) :
    coefficientCohomologyNatTrans f hf hp 0 ≫
        (Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
          (smoothGodementCompactCohomologyZeroIso R G X)).hom =
      (Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G Y)
          (smoothGodementCompactCohomologyZeroIso R G Y)).hom ≫
        coefficientCompactSectionsNatTrans f hf hp := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (SmoothRep R G) (ComplexShape.up ℕ) 0).map
      ((coefficientCompactNatTrans f hf hp).app M) ≫
      (smoothGodementCompactCohomologyZeroIso R G X).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) =
    (smoothGodementCompactCohomologyZeroIso R G Y).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G Y).obj M) ≫
      (coefficientCompactSectionsNatTrans f hf hp).app M
  rw [coefficientCompactNatTrans_app, Functor.map_comp]
  change ((smoothGodementCompactCohomology R G Y 0).map
      (SmoothDirectImage.coefficientMap f hf M) ≫ cohomologyMap f hf hp
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) 0) ≫
      (smoothGodementCompactCohomologyZeroIso R G X).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) = _
  rw [Category.assoc, cohomologyMap_zero, ← Category.assoc,
    (smoothGodementCompactCohomologyZeroIso R G Y).hom.naturality]
  rfl

/-- The same square holds for module homology after termwise invariants. -/
@[reassoc]
theorem coefficientInvariantCohomologyNatTrans_zero (hp : IsProperMap f) :
    coefficientInvariantCohomologyNatTrans f hf hp 0 ≫
        (Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
          (smoothGodementInvariantCompactCohomologyZeroIso R G X)).hom =
      (Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G Y)
          (smoothGodementInvariantCompactCohomologyZeroIso R G Y)).hom ≫
        coefficientInvariantSectionsNatTrans f hf hp := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) 0).map
      ((coefficientInvariantCompactNatTrans f hf hp).app M) ≫
      (smoothGodementInvariantCompactCohomologyZeroIso R G X).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) =
    (smoothGodementInvariantCompactCohomologyZeroIso R G Y).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G Y).obj M) ≫
      (coefficientInvariantSectionsNatTrans f hf hp).app M
  rw [coefficientInvariantCompactNatTrans_app, Functor.map_comp]
  change ((smoothGodementInvariantCompactCohomology R G Y 0).map
      (SmoothDirectImage.coefficientMap f hf M) ≫ invariantCohomologyMap f hf hp
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) 0) ≫
      (smoothGodementInvariantCompactCohomologyZeroIso R G X).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) = _
  rw [Category.assoc, invariantCohomologyMap_zero, ← Category.assoc,
    (smoothGodementInvariantCompactCohomologyZeroIso R G Y).hom.naturality]
  rfl

end Langlands.Cohomology.SmoothGodementCohomology.Spatial
