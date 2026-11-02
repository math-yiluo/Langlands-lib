import Langlands.Sheaf.Equivariant.Godement.Smooth
import Langlands.Sheaf.Equivariant.CoinducedFamilies.Functoriality

/-! # The actual coinduced model of the separate smooth Godement functor -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- The separate smooth Godement functor is naturally isomorphic to smooth
coreflection of actual coinduction of the ordinary stalk-family sheaf. -/
def smoothZeroCoinducedIso :
    smoothZeroFunctor R G X ≅
      smoothInclusion R G X ⋙ CoinducedFamilies.coinducedZeroFunctor ⋙
        smoothCoreflector R :=
  Functor.isoWhiskerLeft (smoothInclusion R G X)
    (Functor.isoWhiskerRight (zeroIso R G X).symm (smoothCoinduction R G X))

/-- The forward component coinduces the inverse ordinary Godement comparison
and applies the actual smooth coreflector. -/
theorem smoothZeroCoinducedIso_hom_app (F : SmoothTopologicalSheaf R G X) :
    (smoothZeroCoinducedIso R G X).hom.app F =
      (smoothCoreflector R).map
        ((coinduction G X (ModuleCat.{u} R)).map
          ((zeroIso R G X).inv.app F.obj)) := rfl

/-- The inverse component coinduces the original ordinary Godement comparison. -/
theorem smoothZeroCoinducedIso_inv_app (F : SmoothTopologicalSheaf R G X) :
    (smoothZeroCoinducedIso R G X).inv.app F =
      (smoothCoreflector R).map
        ((coinduction G X (ModuleCat.{u} R)).map
          ((zeroIso R G X).hom.app F.obj)) := rfl

/-- Coaugment by the smooth-coreflection unit and the actual coinduced germ map. -/
def coinducedSmoothCoaugmentation :
    𝟭 (SmoothTopologicalSheaf R G X) ⟶
      smoothInclusion R G X ⋙ CoinducedFamilies.coinducedZeroFunctor ⋙
        smoothCoreflector R :=
  (smoothAdjunction R).unit ≫
    Functor.whiskerLeft (smoothInclusion R G X)
      (Functor.whiskerRight CoinducedFamilies.coinducedCoaugmentation
        (smoothCoreflector R))

/-- This coaugmentation is the actual adjoint of the coinduced germ map. -/
theorem coinducedSmoothCoaugmentation_app (F : SmoothTopologicalSheaf R G X) :
    (coinducedSmoothCoaugmentation R G X).app F =
      (smoothAdjunction R).homEquiv F _
        ((CoinducedFamilies.coinducedCoaugmentation (R := R)).app F.obj) :=
  ((smoothAdjunction R).homEquiv_unit _ _ _).symm

/-- The actual smooth-subsheaf inclusion recovers the original coinduced germ map. -/
@[reassoc]
theorem coinducedSmoothCoaugmentation_inclusion
    (F : SmoothTopologicalSheaf R G X) :
    (smoothInclusion R G X).map ((coinducedSmoothCoaugmentation R G X).app F) ≫
        (smoothSubsheafι R).app (CoinducedFamilies.coinducedZeroFunctor.obj F.obj) =
      (CoinducedFamilies.coinducedCoaugmentation (R := R)).app F.obj := by
  rw [coinducedSmoothCoaugmentation_app]
  change (smoothInclusion R G X).map
    ((smoothAdjunction R).homEquiv F _
      ((CoinducedFamilies.coinducedCoaugmentation (R := R)).app F.obj)) ≫
      (smoothAdjunction R).counit.app _ = _
  exact ((smoothAdjunction R).homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

/-- The inverse comparison identifies the actual coinduced coaugmentation with
that defined from the ordinary Godement coaugmentation and composite adjunction. -/
@[reassoc]
theorem coinducedSmoothCoaugmentation_comparison
    (F : SmoothTopologicalSheaf R G X) :
    (coinducedSmoothCoaugmentation R G X).app F ≫
        (smoothZeroCoinducedIso R G X).inv.app F =
      (smoothCoaugmentation R G X).app F := by
  change ((smoothAdjunction R).unit.app F ≫
    (smoothCoreflector R).map
      ((coaugmentation R G X).app F.obj ≫
        (coinductionAdjunction G X (ModuleCat.{u} R)).unit.app
          ((zeroFunctor R G X).obj F.obj))) ≫
    (smoothCoreflector R).map
      ((coinduction G X (ModuleCat.{u} R)).map ((zeroIso R G X).hom.app F.obj)) = _
  rw [Category.assoc, ← Functor.map_comp]
  have hn := (coinductionAdjunction G X (ModuleCat.{u} R)).unit.naturality
    ((coaugmentation R G X).app F.obj)
  change (coaugmentation R G X).app F.obj ≫
      (coinductionAdjunction G X (ModuleCat.{u} R)).unit.app
        ((zeroFunctor R G X).obj F.obj) =
    (coinductionAdjunction G X (ModuleCat.{u} R)).unit.app F.obj ≫
      (coinduction G X (ModuleCat.{u} R)).map
        ((toSheaf G X (ModuleCat.{u} R)).map
          ((coaugmentation R G X).app F.obj)) at hn
  rw [hn]
  rw [Category.assoc, ← Functor.map_comp, zeroIso_comm]
  change (smoothAdjunction R).unit.app F ≫
    (smoothCoreflector R).map
      ((coinductionAdjunction G X (ModuleCat.{u} R)).unit.app F.obj ≫
        (coinduction G X (ModuleCat.{u} R)).map
          ((Sheaf.Godement.coaugmentation
            (Cohomology.Flasque.spacePoints (TopCat.of X)) (ModuleCat.{u} R)).app
              ((smoothForget R G X).obj F))) = _
  rw [Functor.map_comp, ← Category.assoc]
  change _ = (smoothCoinductionAdjunction R G X).unit.app F ≫ _
  rw [smoothCoinductionAdjunction, Adjunction.comp_unit_app]
  rfl

/-- The natural comparison carries the separate smooth Godement coaugmentation
to the smooth coreflection of the actual coinduced germ map. -/
@[reassoc]
theorem smoothCoaugmentation_coinducedIso
    (F : SmoothTopologicalSheaf R G X) :
    (smoothCoaugmentation R G X).app F ≫
        (smoothZeroCoinducedIso R G X).hom.app F =
      (coinducedSmoothCoaugmentation R G X).app F := by
  rw [← coinducedSmoothCoaugmentation_comparison R G X F, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

end Langlands.Sheaf.Equivariant.Godement
