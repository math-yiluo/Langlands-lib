import Langlands.Sheaf.Equivariant.SmoothDirectImage
import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Langlands.Sheaf.Equivariant.ProperCompactSections
import Langlands.Sheaf.Equivariant.LocalSupportComparison

/-! # Proper spatial pullback of compact sections of smooth sheaves -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.ProperSmoothCompactSections

open CategoryTheory Opposite

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- An actual map into ordinary direct image gives compact pullback between the
proved smooth compact-section representations. -/
def pullback (hp : IsProperMap f)
    {K : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    (smoothSheafCompactSections R G Y).obj K ⟶
      (smoothSheafCompactSections R G X).obj F :=
  ObjectProperty.homMk
    ((LocalCompactSections.stalkComparison R G Y).inv.app K.obj ≫
      ProperCompactSections.pullback f hf hp b ≫
        (LocalCompactSections.stalkComparison R G X).hom.app F.obj)

omit [IsTopologicalGroup G] in
/-- The pullback applies the given sheaf map on its original global sections. -/
@[simp]
theorem pullback_apply (hp : IsProperMap f)
    {K : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj)
    (s : (smoothSheafCompactSections R G Y).obj K) :
    ((Langlands.SmoothRep.hom (pullback f hf hp b)) s).val =
      (b.hom.app (op ActionOpens.top)).hom s.val := rfl

omit [IsTopologicalGroup G] in
/-- The local-support and stalk-support pullbacks agree on the same sections. -/
theorem pullback_comparison (hp : IsProperMap f)
    {K : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    (LocalCompactSections.stalkComparison R G Y).hom.app K.obj ≫
        Langlands.SmoothRep.toRep.map (pullback f hf hp b) =
      ProperCompactSections.pullback f hf hp b ≫
        (LocalCompactSections.stalkComparison R G X).hom.app F.obj := by
  ext s
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalGroup G] in
/-- Forgetting compact support retains the original global sheaf map. -/
theorem pullback_inclusion_triangle (hp : IsProperMap f)
    {K : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    Langlands.SmoothRep.toRep.map (pullback f hf hp b) ≫
        (CompactSections.inclusion R G X).app F.obj =
      (CompactSections.inclusion R G Y).app K.obj ≫
        (sectionRepresentation R G Y).map b ≫
          (ProperCompactSections.globalIso f hf).hom.app F.obj := by
  ext s
  rfl

omit [IsTopologicalGroup G] in
@[simp]
theorem pullback_id (F : SmoothTopologicalSheaf R G X) :
    pullback (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id (𝟙 F.obj) =
      𝟙 ((smoothSheafCompactSections R G X).obj F) := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

omit [IsTopologicalGroup G] in
theorem pullback_precomp (hp : IsProperMap f)
    {K K' : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    (a : K' ⟶ K)
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    pullback f hf hp (a.hom ≫ b) =
      (smoothSheafCompactSections R G Y).map a ≫ pullback f hf hp b := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

omit [IsTopologicalGroup G] in
theorem pullback_postcomp (hp : IsProperMap f)
    {K : SmoothTopologicalSheaf R G Y} {F F' : SmoothTopologicalSheaf R G X}
    (a : F ⟶ F')
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    pullback f hf hp (b ≫ (DirectImage.sheaf f hf (ModuleCat.{u} R)).map a.hom) =
      pullback f hf hp b ≫ (smoothSheafCompactSections R G X).map a := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

omit [IsTopologicalGroup G] in
/-- Actual coefficient maps compose with proper spatial pullback. -/
theorem pullback_comp
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    {K : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    {L : SmoothTopologicalSheaf R G Z}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj)
    (a : L.obj ⟶ (DirectImage.sheaf g hg (ModuleCat.{u} R)).obj K.obj) :
    pullback (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) (a ≫ (DirectImage.sheaf g hg (ModuleCat.{u} R)).map b) =
      pullback g hg hq a ≫ pullback f hf hp b := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

section SmoothImage

variable [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]

/-- Proper pullback from the smooth direct image is natural in smooth sheaves. -/
def natTrans (hp : IsProperMap f) :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothSheafCompactSections R G Y ⟶
      smoothSheafCompactSections R G X where
  app F := pullback f hf hp ((SmoothDirectImage.inclusion f hf).app F)
  naturality _ _ _ := by
    apply ObjectProperty.hom_ext
    ext s
    rfl

omit [HasStableNeighbourhoods G X] in
/-- Proper spatial pullback retains the underlying original section. -/
@[simp]
theorem natTrans_apply (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X)
    (s : (smoothSheafCompactSections R G Y).obj ((SmoothDirectImage.functor f hf).obj F)) :
    ((Langlands.SmoothRep.hom ((natTrans f hf hp).app F)) s).val = s.val.val := rfl

omit [HasStableNeighbourhoods G X] in
/-- The universal smooth lift gives precisely the original compact pullback. -/
theorem lift_pullback (hp : IsProperMap f)
    {K : SmoothTopologicalSheaf R G Y} {F : SmoothTopologicalSheaf R G X}
    (b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F.obj) :
    (smoothSheafCompactSections R G Y).map (SmoothDirectImage.lift f hf b) ≫
        (natTrans f hf hp).app F =
      pullback f hf hp b := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [HasStableNeighbourhoods G X] in
/-- The smooth spatial map commutes with the actual global-section inclusions. -/
theorem natTrans_inclusion_triangle (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    Langlands.SmoothRep.toRep.map ((natTrans f hf hp).app F) ≫
        (CompactSections.inclusion R G X).app F.obj =
      (CompactSections.inclusion R G Y).app ((SmoothDirectImage.functor f hf).obj F).obj ≫
        (sectionRepresentation R G Y).map ((SmoothDirectImage.inclusion f hf).app F) ≫
          (ProperCompactSections.globalIso f hf).hom.app F.obj := by
  ext s
  rfl

/-- The smooth identity comparison gives identity on compact sections. -/
@[simp]
theorem natTrans_id (F : SmoothTopologicalSheaf R G X) :
    (smoothSheafCompactSections R G X).map
          ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        (natTrans (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
          isProperMap_id).app F =
      𝟙 ((smoothSheafCompactSections R G X).obj F) := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

omit [HasStableNeighbourhoods G X] in
/-- Spatial compact pullback respects the actual lax comparison of smooth images. -/
theorem natTrans_comp
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothSheafCompactSections R G Z).map ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        (natTrans (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
          (hq.comp hp)).app F =
      (natTrans g hg hq).app ((SmoothDirectImage.functor f hf).obj F) ≫
        (natTrans f hf hp).app F := by
  apply ObjectProperty.hom_ext
  ext s
  rfl

end SmoothImage

end Langlands.Sheaf.Equivariant.ProperSmoothCompactSections
