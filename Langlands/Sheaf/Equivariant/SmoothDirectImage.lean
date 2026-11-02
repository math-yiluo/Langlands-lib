import Langlands.Sheaf.Equivariant.DirectImage
import Langlands.Sheaf.Equivariant.SmoothAbelian

/-! # Smooth direct image along continuous equivariant maps -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.SmoothDirectImage

open CategoryTheory Opposite

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Direct image in smooth sheaves is the smooth part of the full ordinary-open
transport-sheaf direct image. -/
def functor : SmoothTopologicalSheaf R G X ⥤ SmoothTopologicalSheaf R G Y :=
  smoothInclusion R G X ⋙ DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ smoothCoreflector R

/-- Smooth direct image is additive on the actual sheaf morphisms. -/
instance additive : (functor (R := R) f hf).Additive where
  map_add {_ _ a b} := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl

/-- The smooth direct image is an actual equivariant subsheaf of the full
ordinary direct image. -/
def inclusion : functor f hf ⋙ smoothInclusion R G Y ⟶
    smoothInclusion R G X ⋙ DirectImage.sheaf f hf (ModuleCat.{u} R) :=
  Functor.whiskerLeft (smoothInclusion R G X ⋙ DirectImage.sheaf f hf (ModuleCat.{u} R))
    (smoothSubsheafι R)

/-- Each smooth-image inclusion is a monomorphism of ordinary equivariant sheaves. -/
instance mono_inclusion_app (F : SmoothTopologicalSheaf R G X) :
    Mono ((inclusion f hf).app F) :=
  inferInstanceAs (Mono ((smoothSubsheafι R).app _))

/-- The universal property retains every map from a smooth sheaf to the full
direct image, with no condition on the fibres of the spatial map. -/
def homEquiv (F : SmoothTopologicalSheaf R G X) (K : SmoothTopologicalSheaf R G Y) :
    (K ⟶ (functor f hf).obj F) ≃
      (K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :=
  ((smoothAdjunction R).homEquiv K _).symm

/-- Factor an equivariant sheaf map from a smooth sheaf through smooth direct image. -/
def lift {F : SmoothTopologicalSheaf R G X} {K : SmoothTopologicalSheaf R G Y}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    K ⟶ (functor f hf).obj F :=
  (homEquiv f hf F K).symm b

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
@[reassoc (attr := simp)]
theorem lift_inclusion {F : SmoothTopologicalSheaf R G X}
    {K : SmoothTopologicalSheaf R G Y}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    (smoothInclusion R G Y).map (lift f hf b) ≫ (inclusion f hf).app F = b := rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- Equality into smooth direct image can be tested in the full direct image. -/
theorem hom_ext {F : SmoothTopologicalSheaf R G X}
    {K : SmoothTopologicalSheaf R G Y} {a b : K ⟶ (functor f hf).obj F}
    (h : (smoothInclusion R G Y).map a ≫ (inclusion f hf).app F =
      (smoothInclusion R G Y).map b ≫ (inclusion f hf).app F) : a = b :=
  (homEquiv f hf F K).injective h

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
@[simp]
theorem lift_apply {F : SmoothTopologicalSheaf R G X}
    {K : SmoothTopologicalSheaf R G Y}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj)
    (U : ActionOpens G Y) (s : K.obj.obj.obj (op U)) :
    (((lift f hf b).hom.hom.app (op U)).hom s).val = (b.hom.app (op U)).hom s := rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- The inclusion forgets precisely the proof of local smoothness. -/
@[simp]
theorem inclusion_apply (F : SmoothTopologicalSheaf R G X) (U : ActionOpens G Y)
    (s : ((functor f hf).obj F).obj.obj.obj (op U)) :
    (((inclusion f hf).app F).hom.app (op U)).hom s = s.val := rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- Direct image on a sheaf morphism is its original inverse-image-open component,
restricted to locally smooth sections. -/
@[simp]
theorem map_apply {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F')
    (U : ActionOpens G Y) (s : ((functor f hf).obj F).obj.obj.obj (op U)) :
    ((((functor f hf).map a).hom.hom.app (op U)).hom s).val =
      (a.hom.hom.app (op ((DirectImage.preimage f hf).obj U))).hom s.val := rfl

/-- The identity spatial map has smooth direct image naturally isomorphic to
the original smooth sheaf. The displayed orientation is the adjunction unit. -/
def idIso : 𝟭 (SmoothTopologicalSheaf R G X) ≅
    functor (R := R) (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) := by
  change 𝟭 _ ≅ smoothInclusion R G X ⋙ smoothCoreflector R
  letI : IsIso (smoothAdjunction (G := G) (X := X) R).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  exact asIso (smoothAdjunction (G := G) (X := X) R).unit

/-- The identity comparison retains each original section. -/
@[simp]
theorem idIso_hom_apply (F : SmoothTopologicalSheaf R G X)
    (U : ActionOpens G X) (s : F.obj.obj.obj (op U)) :
    ((((idIso (R := R) (G := G) (X := X)).hom.app F).hom.hom.app (op U)).hom s).val = s :=
  rfl

/-- Comparison from iterated smooth direct image to smooth direct image along
the composite, obtained by the two actual subsheaf inclusions. -/
def compMap (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) :
    functor (R := R) f hf ⋙ functor g hg ⟶
      functor (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) where
  app F := lift (g.comp f) _ ((inclusion g hg).app ((functor f hf).obj F) ≫
    (DirectImage.sheaf g hg (ModuleCat.{u} R)).map ((inclusion f hf).app F))
  naturality _ _ a := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- The composite comparison is characterized by its map into the full
ordinary direct image. -/
@[reassoc (attr := simp)]
theorem compMap_inclusion (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothInclusion R G Z).map ((compMap f hf g hg).app F) ≫
        (inclusion (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])).app F =
      (inclusion g hg).app ((functor f hf).obj F) ≫
        (DirectImage.sheaf g hg (ModuleCat.{u} R)).map ((inclusion f hf).app F) :=
  rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- Iterated smoothing is sent to the original section in the composite image. -/
@[simp]
theorem compMap_apply (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) (U : ActionOpens G Z)
    (s : ((functor g hg).obj ((functor f hf).obj F)).obj.obj.obj (op U)) :
    ((((compMap f hf g hg).app F).hom.hom.app (op U)).hom s).val = s.val.val := rfl

/-- Inserting the identity before a spatial map has the expected unit law. -/
theorem compMap_id_left (F : SmoothTopologicalSheaf R G X) :
    (functor f hf).map ((idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        (compMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) f hf).app F =
      𝟙 ((functor f hf).obj F) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- Inserting the identity after a spatial map has the expected unit law. -/
theorem compMap_id_right (F : SmoothTopologicalSheaf R G X) :
    (idIso (R := R) (G := G) (X := Y)).hom.app ((functor f hf).obj F) ≫
        (compMap f hf (ContinuousMap.id Y) (fun (_ : G) (_ : Y) => rfl)).app F =
      𝟙 ((functor f hf).obj F) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

omit [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- The two comparisons from three iterated smooth direct images agree. -/
theorem compMap_assoc {W : Type u} [TopologicalSpace W] [MulAction G W]
    [ContinuousConstSMul G W] [HasStableNeighbourhoods G W]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (h : C(Z, W)) (hh : ∀ (k : G) (z : Z), h (k • z) = k • h z)
    (F : SmoothTopologicalSheaf R G X) :
    (functor h hh).map ((compMap f hf g hg).app F) ≫
        (compMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) h hh).app F =
      (compMap g hg h hh).app ((functor f hf).obj F) ≫
        (compMap f hf (h.comp g)
          (fun k y => by change h (g (k • y)) = k • h (g y); rw [hg, hh])).app F := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

end Langlands.Sheaf.Equivariant.SmoothDirectImage
