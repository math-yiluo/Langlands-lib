import Langlands.Sheaf.Equivariant.Godement.SmoothCoinduced
import Langlands.Sheaf.Equivariant.CoinducedFamilies.Spatial
import Langlands.Sheaf.Equivariant.SmoothDirectImageCoreflector

/-! # Actual spatial maps on the separate smooth Godement degree-zero functor -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Sheaf.Equivariant.Godement.SmoothSpatial

open CategoryTheory
open CoinducedFamilies CoinducedFamilies.Spatial

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The actual coinduced spatial map after the smooth-image inclusion and
smooth coreflection, followed by the inverse-image smoothness comparison. -/
def coinducedNatTrans :
    SmoothDirectImage.functor (R := R) f hf ⋙
        (smoothInclusion R G Y ⋙ coinducedZeroFunctor ⋙ smoothCoreflector R) ⟶
      (smoothInclusion R G X ⋙ coinducedZeroFunctor ⋙ smoothCoreflector R) ⋙
        SmoothDirectImage.functor f hf :=
  Functor.whiskerRight (SmoothDirectImage.inclusion f hf)
      (coinducedZeroFunctor ⋙ smoothCoreflector R) ≫
    Functor.whiskerLeft (smoothInclusion R G X)
      (Functor.whiskerRight (coinducedSpatialNatTrans f hf) (smoothCoreflector R)) ≫
    Functor.whiskerLeft (smoothInclusion R G X ⋙ coinducedZeroFunctor)
      (SmoothDirectImage.coreflectorIso f hf).hom

/-- A component of the constructed spatial transformation in the coinduced model. -/
abbrev coinducedMap (F : SmoothTopologicalSheaf R G X) :=
  (coinducedNatTrans (R := R) f hf).app F

/-- Before coreflection, first include the smooth image and then use the
actual coinduced spatial map. -/
def underlyingMap (F : SmoothTopologicalSheaf R G X) :
    (coinducedZeroFunctor (R := R) (G := G) (X := Y)).obj
        (((SmoothDirectImage.functor f hf).obj F).obj) ⟶
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj
        ((coinducedZeroFunctor (R := R) (G := G) (X := X)).obj F.obj) :=
  coinducedZeroFunctor.map ((SmoothDirectImage.inclusion f hf).app F) ≫
    coinducedSpatialMap f hf F.obj

/-- The component is built from actual inclusions, the spatial stalk map and
coreflection; no spatial map is supplied as input. -/
theorem coinducedMap_eq (F : SmoothTopologicalSheaf R G X) :
    coinducedMap f hf F =
      (smoothCoreflector R).map
        (coinducedZeroFunctor.map ((SmoothDirectImage.inclusion f hf).app F) ≫
          coinducedSpatialMap f hf F.obj) ≫
        (SmoothDirectImage.coreflectorIso f hf).hom.app
          (coinducedZeroFunctor.obj F.obj) := by
  simp only [coinducedMap, coinducedNatTrans, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  rfl

/-- The component factors through the constructed map before coreflection. -/
theorem coinducedMap_eq_underlying (F : SmoothTopologicalSheaf R G X) :
    coinducedMap f hf F =
      (smoothCoreflector R).map (underlyingMap f hf F) ≫
        (SmoothDirectImage.coreflectorIso f hf).hom.app
          (coinducedZeroFunctor.obj F.obj) :=
  coinducedMap_eq f hf F

/-- Including twice recovers exactly the original coinduced spatial map
preceded by the coinduced actual smooth-image inclusion. -/
@[reassoc]
theorem coinducedMap_inclusion (F : SmoothTopologicalSheaf R G X) :
    (smoothInclusion R G Y).map (coinducedMap f hf F) ≫
        (SmoothDirectImage.inclusion f hf).app
          ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) ≫
        (DirectImage.sheaf f hf (ModuleCat.{u} R)).map
          ((smoothSubsheafι R).app (coinducedZeroFunctor.obj F.obj)) =
      (smoothSubsheafι R).app
          ((coinducedZeroFunctor (R := R) (G := G) (X := Y)).obj
            (((SmoothDirectImage.functor f hf).obj F).obj)) ≫
        (coinducedZeroFunctor (R := R) (G := G) (X := Y)).map
          ((SmoothDirectImage.inclusion f hf).app F) ≫
        coinducedSpatialMap f hf F.obj := by
  rw [coinducedMap_eq]
  rfl

/-- The two actual inclusions detect equality of maps to the smooth direct
image of the coinduced smooth Godement sheaf. -/
theorem coinduced_hom_ext {F : SmoothTopologicalSheaf R G X}
    {K : SmoothTopologicalSheaf R G Y}
    {a b : K ⟶ (SmoothDirectImage.functor f hf).obj
      ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj))}
    (h : (smoothInclusion R G Y).map a ≫
        (SmoothDirectImage.inclusion f hf).app
          ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) ≫
        (DirectImage.sheaf f hf (ModuleCat.{u} R)).map
          ((smoothSubsheafι R).app (coinducedZeroFunctor.obj F.obj)) =
      (smoothInclusion R G Y).map b ≫
        (SmoothDirectImage.inclusion f hf).app
          ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) ≫
        (DirectImage.sheaf f hf (ModuleCat.{u} R)).map
          ((smoothSubsheafι R).app (coinducedZeroFunctor.obj F.obj))) : a = b := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t => t.hom.app U s) h

/-- The constructed smooth spatial map respects the actual adjoint germ
coaugmentation in the coinduced model. -/
@[reassoc]
theorem coaugmentation_coinducedMap (F : SmoothTopologicalSheaf R G X) :
    (coinducedSmoothCoaugmentation R G Y).app
        ((SmoothDirectImage.functor f hf).obj F) ≫ coinducedMap f hf F =
      (SmoothDirectImage.functor f hf).map
        ((coinducedSmoothCoaugmentation R G X).app F) := by
  apply coinduced_hom_ext f hf
  simp only [Functor.map_comp, Category.assoc]
  rw [coinducedMap_inclusion]
  rw [← Category.assoc, coinducedSmoothCoaugmentation_inclusion]
  have hn := (coinducedCoaugmentation (R := R)).naturality
    ((SmoothDirectImage.inclusion f hf).app F)
  change (SmoothDirectImage.inclusion f hf).app F ≫
      (coinducedCoaugmentation (R := R)).app
        ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) =
    (coinducedCoaugmentation (R := R)).app ((SmoothDirectImage.functor f hf).obj F).obj ≫
      coinducedZeroFunctor.map ((SmoothDirectImage.inclusion f hf).app F) at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    coaugmentation_coinducedSpatialMap]
  have hi := (SmoothDirectImage.inclusion f hf).naturality
    ((coinducedSmoothCoaugmentation R G X).app F)
  change (smoothInclusion R G Y).map
      ((SmoothDirectImage.functor f hf).map
        ((coinducedSmoothCoaugmentation R G X).app F)) ≫
        (SmoothDirectImage.inclusion f hf).app
          ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) =
    (SmoothDirectImage.inclusion f hf).app F ≫
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).map
        ((smoothInclusion R G X).map
          ((coinducedSmoothCoaugmentation R G X).app F)) at hi
  rw [← Category.assoc, hi, Category.assoc, ← Functor.map_comp,
    coinducedSmoothCoaugmentation_inclusion]

/-- The coinduced smooth spatial map respects the actual identity comparison
of smooth direct image. -/
@[reassoc]
theorem coinducedMap_id (F : SmoothTopologicalSheaf R G X) :
    (smoothInclusion R G X ⋙
        coinducedZeroFunctor (R := R) (G := G) (X := X) ⋙ smoothCoreflector R).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        coinducedMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app
        ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) := by
  rw [coinducedMap_eq, coinducedSpatialMap_id]
  change (smoothCoreflector R).map
      ((coinducedZeroFunctor (R := R) (G := G) (X := X)).map
        ((smoothInclusion R G X).map
          ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F))) ≫
      ((smoothCoreflector R).map
        ((coinducedZeroFunctor (R := R) (G := G) (X := X)).map
          ((SmoothDirectImage.inclusion (ContinuousMap.id X)
            (fun (_ : G) (_ : X) => rfl)).app F)) ≫ _) = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  have hi : (smoothInclusion R G X).map
      ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
      (SmoothDirectImage.inclusion (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl)).app F = 𝟙 F.obj := rfl
  rw [hi]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact SmoothDirectImage.coreflectorIso_id _

omit [HasStableNeighbourhoods G X] in
/-- The underlying spatial maps retain the actual smooth-direct-image
composition comparison. -/
@[reassoc]
theorem underlyingMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) :
    (coinducedZeroFunctor (R := R) (G := G) (X := Z)).map
        ((smoothInclusion R G Z).map ((SmoothDirectImage.compMap f hf g hg).app F)) ≫
        underlyingMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      underlyingMap g hg ((SmoothDirectImage.functor f hf).obj F) ≫
        (DirectImage.sheaf g hg (ModuleCat.{u} R)).map (underlyingMap f hf F) := by
  have hq := (coinducedSpatialNatTrans (R := R) g hg).naturality
    ((SmoothDirectImage.inclusion f hf).app F)
  change (coinducedZeroFunctor (R := R) (G := G) (X := Z)).map
      ((DirectImage.sheaf g hg (ModuleCat.{u} R)).map
        ((SmoothDirectImage.inclusion f hf).app F)) ≫
      coinducedSpatialMap g hg ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) =
    coinducedSpatialMap g hg (((SmoothDirectImage.functor f hf).obj F).obj) ≫
      (DirectImage.sheaf g hg (ModuleCat.{u} R)).map
        ((coinducedZeroFunctor (R := R) (G := G) (X := Y)).map
          ((SmoothDirectImage.inclusion f hf).app F)) at hq
  dsimp only [underlyingMap]
  rw [← Functor.map_comp_assoc, SmoothDirectImage.compMap_inclusion,
    Functor.map_comp, coinducedSpatialMap_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((coinducedZeroFunctor (R := R) (G := G) (X := Z)).map
      ((DirectImage.sheaf g hg (ModuleCat.{u} R)).map
        ((SmoothDirectImage.inclusion f hf).app F))), hq, Category.assoc]

/-- The constructed smooth spatial maps respect the actual lax comparison
from iterated smooth direct image to the composite image. -/
@[reassoc]
theorem coinducedMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothInclusion R G Z ⋙
        coinducedZeroFunctor (R := R) (G := G) (X := Z) ⋙ smoothCoreflector R).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        coinducedMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      coinducedMap g hg ((SmoothDirectImage.functor f hf).obj F) ≫
        (SmoothDirectImage.functor g hg).map (coinducedMap f hf F) ≫
        (SmoothDirectImage.compMap f hf g hg).app
          ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) := by
  have hn := (SmoothDirectImage.coreflectorIso (R := R) g hg).hom.naturality
    (underlyingMap f hf F)
  change (smoothCoreflector R).map
      ((DirectImage.sheaf g hg (ModuleCat.{u} R)).map (underlyingMap f hf F)) ≫
      (SmoothDirectImage.coreflectorIso g hg).hom.app
        ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj (coinducedZeroFunctor.obj F.obj)) =
    (SmoothDirectImage.coreflectorIso g hg).hom.app
        ((coinducedZeroFunctor (R := R) (G := G) (X := Y)).obj
          (((SmoothDirectImage.functor f hf).obj F).obj)) ≫
      (SmoothDirectImage.functor g hg).map
        ((smoothCoreflector R).map (underlyingMap f hf F)) at hn
  simp only [coinducedMap_eq_underlying]
  change (smoothCoreflector R).map
      ((coinducedZeroFunctor (R := R) (G := G) (X := Z)).map
        ((smoothInclusion R G Z).map
          ((SmoothDirectImage.compMap f hf g hg).app F))) ≫
      ((smoothCoreflector R).map (underlyingMap (g.comp f) _ F) ≫ _) = _
  rw [← Functor.map_comp_assoc, underlyingMap_comp, Functor.map_comp]
  rw [Category.assoc, ← SmoothDirectImage.coreflectorIso_comp f hf g hg]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((smoothCoreflector R).map
      ((DirectImage.sheaf g hg (ModuleCat.{u} R)).map (underlyingMap f hf F))),
    hn, Category.assoc]

/-- Transport the actual coinduced spatial transformation to the separate
smooth Godement degree-zero functor. -/
def zeroNatTrans :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothZeroFunctor R G Y ⟶
      smoothZeroFunctor R G X ⋙ SmoothDirectImage.functor f hf :=
  Functor.whiskerLeft (SmoothDirectImage.functor f hf)
      (smoothZeroCoinducedIso R G Y).hom ≫
    coinducedNatTrans f hf ≫
    Functor.whiskerRight (smoothZeroCoinducedIso R G X).inv
      (SmoothDirectImage.functor f hf)

/-- The resulting spatial map on the original separate smooth Godement object. -/
abbrev zeroMap (F : SmoothTopologicalSheaf R G X) :=
  (zeroNatTrans (R := R) f hf).app F

/-- Naturality uses every original morphism of smooth equivariant sheaves. -/
@[reassoc]
theorem zeroMap_naturality {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothZeroFunctor R G Y).map ((SmoothDirectImage.functor f hf).map a) ≫
        zeroMap f hf F' =
      zeroMap f hf F ≫
        (SmoothDirectImage.functor f hf).map ((smoothZeroFunctor R G X).map a) :=
  (zeroNatTrans f hf).naturality a

/-- The map is conjugation by the proved natural coinduced comparison. -/
theorem zeroMap_eq (F : SmoothTopologicalSheaf R G X) :
    zeroMap f hf F =
      (smoothZeroCoinducedIso R G Y).hom.app ((SmoothDirectImage.functor f hf).obj F) ≫
        coinducedMap f hf F ≫
        (SmoothDirectImage.functor f hf).map ((smoothZeroCoinducedIso R G X).inv.app F) :=
  rfl

/-- The coinduced comparison intertwines the two constructed spatial maps. -/
@[reassoc]
theorem zeroMap_comparison (F : SmoothTopologicalSheaf R G X) :
    zeroMap f hf F ≫
        (SmoothDirectImage.functor f hf).map ((smoothZeroCoinducedIso R G X).hom.app F) =
      (smoothZeroCoinducedIso R G Y).hom.app ((SmoothDirectImage.functor f hf).obj F) ≫
        coinducedMap f hf F := by
  rw [zeroMap_eq]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl

/-- The spatial map preserves the actual separate smooth Godement coaugmentation. -/
@[reassoc]
theorem coaugmentation_zeroMap (F : SmoothTopologicalSheaf R G X) :
    (smoothCoaugmentation R G Y).app ((SmoothDirectImage.functor f hf).obj F) ≫
        zeroMap f hf F =
      (SmoothDirectImage.functor f hf).map ((smoothCoaugmentation R G X).app F) := by
  rw [zeroMap_eq]
  erw [smoothCoaugmentation_coinducedIso_assoc,
    coaugmentation_coinducedMap_assoc, ← Functor.map_comp,
    coinducedSmoothCoaugmentation_comparison]

/-- The separate smooth Godement spatial map respects the actual identity
comparison of smooth direct image. -/
@[reassoc]
theorem zeroMap_id (F : SmoothTopologicalSheaf R G X) :
    (smoothZeroFunctor R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        zeroMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app
        ((smoothZeroFunctor R G X).obj F) := by
  have hn := (smoothZeroCoinducedIso R G X).hom.naturality
    ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F)
  have he := (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.naturality
    ((smoothZeroCoinducedIso R G X).inv.app F)
  rw [zeroMap_eq, ← Category.assoc
    ((smoothZeroFunctor R G X).map
      ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F)), hn,
    Category.assoc]
  erw [coinducedMap_id_assoc (R := R) (G := G) (X := X) F]
  erw [← he, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- The separate smooth Godement spatial maps respect the lax spatial
composition comparison without assuming that comparison invertible. -/
@[reassoc]
theorem zeroMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothZeroFunctor R G Z).map ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        zeroMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      zeroMap g hg ((SmoothDirectImage.functor f hf).obj F) ≫
        (SmoothDirectImage.functor g hg).map (zeroMap f hf F) ≫
        (SmoothDirectImage.compMap f hf g hg).app ((smoothZeroFunctor R G X).obj F) := by
  let hgf : ∀ (k : G) (x : X), (g.comp f) (k • x) = k • (g.comp f) x :=
    fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]
  have he := (smoothZeroCoinducedIso R G Z).hom.naturality
    ((SmoothDirectImage.compMap f hf g hg).app F)
  have hc := (SmoothDirectImage.compMap f hf g hg).naturality
    ((smoothZeroCoinducedIso R G X).hom.app F)
  change (SmoothDirectImage.functor g hg).map
      ((SmoothDirectImage.functor f hf).map ((smoothZeroCoinducedIso R G X).hom.app F)) ≫
      (SmoothDirectImage.compMap f hf g hg).app
        ((smoothCoreflector R).obj (coinducedZeroFunctor.obj F.obj)) =
    (SmoothDirectImage.compMap f hf g hg).app ((smoothZeroFunctor R G X).obj F) ≫
      (SmoothDirectImage.functor (g.comp f) hgf).map
        ((smoothZeroCoinducedIso R G X).hom.app F) at hc
  apply (cancel_mono ((SmoothDirectImage.functor (g.comp f) hgf).map
    ((smoothZeroCoinducedIso R G X).hom.app F))).1
  simp only [Category.assoc]
  rw [zeroMap_comparison (g.comp f) hgf F]
  rw [← Category.assoc
    ((smoothZeroFunctor R G Z).map ((SmoothDirectImage.compMap f hf g hg).app F)),
    he, Category.assoc]
  erw [coinducedMap_comp (R := R) f hf g hg F]
  rw [← hc]
  erw [← CategoryTheory.Functor.map_comp_assoc, zeroMap_comparison f hf F]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (zeroMap g hg ((SmoothDirectImage.functor f hf).obj F)),
    zeroMap_comparison g hg ((SmoothDirectImage.functor f hf).obj F), Category.assoc]
  rfl

end Langlands.Sheaf.Equivariant.Godement.SmoothSpatial
