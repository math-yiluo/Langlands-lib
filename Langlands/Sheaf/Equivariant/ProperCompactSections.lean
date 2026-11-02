import Langlands.Sheaf.Equivariant.DirectImage
import Langlands.Sheaf.Equivariant.LocalSupport
import Mathlib.Topology.Maps.Proper.Basic

/-! # Compact sections along proper continuous equivariant maps -/

noncomputable section

universe u v r w

namespace Langlands.Sheaf.Equivariant.ProperCompactSections

open CategoryTheory TopologicalSpace Opposite

variable {R : Type r} [CommRing R] {G : Type v} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
  (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{w} R)

/-- The full transport presheaf on the target, evaluated on inverse opens. -/
abbrev pushed := (DirectImage.presheaf f hf (ModuleCat.{w} R)).obj F

/-- A zero target restriction gives a zero source restriction on its inverse open. -/
theorem vanishesNear
    (s : (pushed f hf F).obj (op ActionOpens.top)) (x : X)
    (hs : Langlands.Sheaf.LocalSupport.VanishesNear
      (LocalCompactSections.ordinary (pushed f hf F)) s (f x)) :
    Langlands.Sheaf.LocalSupport.VanishesNear
      (LocalCompactSections.ordinary F) s x := by
  obtain ⟨U, hxU, hU⟩ := hs
  exact ⟨(Opens.map (TopCat.ofHom f)).obj U, hxU, hU⟩

/-- The source support is contained in the inverse image of the target support. -/
theorem support_subset
    (s : (pushed f hf F).obj (op ActionOpens.top)) :
    Langlands.Sheaf.LocalSupport.support (LocalCompactSections.ordinary F) s ⊆
      f ⁻¹' Langlands.Sheaf.LocalSupport.support
        (LocalCompactSections.ordinary (pushed f hf F)) s := by
  intro x hx hs
  exact hx (vanishesNear f hf F s x hs)

/-- Properness and closedness of local support preserve all compact sections. -/
theorem preserves_compactSupport (hp : IsProperMap f)
    (s : (pushed f hf F).obj (op ActionOpens.top))
    (hs : IsCompact (Langlands.Sheaf.LocalSupport.support
      (LocalCompactSections.ordinary (pushed f hf F)) s)) :
    IsCompact (Langlands.Sheaf.LocalSupport.support
      (LocalCompactSections.ordinary F) s) :=
  (hp.isCompact_preimage hs).of_isClosed_subset
    (Langlands.Sheaf.LocalSupport.isClosed_support
      (LocalCompactSections.ordinary F) s) (support_subset f hf F s)

variable [ContinuousConstSMul G X] [ContinuousConstSMul G Y]

/-- Restrict the unchanged original global section and group action to compact support. -/
def map (hp : IsProperMap f) :
    (LocalCompactSections.representation (pushed f hf F)).IntertwiningMap
      (LocalCompactSections.representation F) where
  toLinearMap :=
    { toFun := fun s => ⟨s.val, preserves_compactSupport f hf F hp s.val s.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

@[simp]
theorem map_apply (hp : IsProperMap f)
    (s : Langlands.Sheaf.LocalSupport.submodule
      (LocalCompactSections.ordinary (pushed f hf F))) :
    (map f hf F hp s).val = s.val := rfl

/-- Proper spatial pullback of compact sections is natural in every transport presheaf. -/
def presheafNatTrans (hp : IsProperMap f) :
    DirectImage.presheaf f hf (ModuleCat.{w} R) ⋙
        LocalCompactSections.presheafFunctor R G Y ⟶
      LocalCompactSections.presheafFunctor R G X where
  app F := Rep.ofHom (map f hf F hp)
  naturality _ _ _ := by ext s; rfl

/-- The original global-section representations agree along direct image. -/
def globalIso :
    DirectImage.sheaf f hf (ModuleCat.{w} R) ⋙ LocalCompactSections.globalFunctor R G Y ≅
      LocalCompactSections.globalFunctor R G X := Iso.refl _

/-- Proper spatial pullback of the full compact-section functor on arbitrary sheaves. -/
def natTrans (hp : IsProperMap f) :
    DirectImage.sheaf f hf (ModuleCat.{w} R) ⋙ LocalCompactSections.functor R G Y ⟶
      LocalCompactSections.functor R G X where
  app F := (presheafNatTrans f hf hp).app F.obj
  naturality _ _ _ := by ext s; rfl

/-- The compact-section map commutes with the actual inclusions into global sections. -/
theorem inclusion_triangle (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{w} R)) :
    (natTrans f hf hp).app F ≫ (LocalCompactSections.inclusion R G X).app F =
      (LocalCompactSections.inclusion R G Y).app
          ((DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F) ≫
        (globalIso f hf).hom.app F := by
  ext s
  rfl

/-- Identity spatial pullback keeps every original compact section. -/
@[simp]
theorem natTrans_id (F : TopologicalSheaf G X (ModuleCat.{w} R)) :
    (natTrans (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id).app F =
      𝟙 ((LocalCompactSections.functor R G X).obj F) := by
  ext s
  rfl

/-- Spatial pullback along a composite is the composite of the two actual maps. -/
theorem natTrans_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : TopologicalSheaf G X (ModuleCat.{w} R)) :
    (natTrans (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp)).app F =
      (natTrans g hg hq).app ((DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F) ≫
        (natTrans f hf hp).app F := by
  ext s
  rfl

variable {K : TopologicalSheaf G Y (ModuleCat.{w} R)}
  {F : TopologicalSheaf G X (ModuleCat.{w} R)}

/-- Any actual coefficient/sheaf map into the direct image induces compact pullback. -/
def pullback (hp : IsProperMap f)
    (b : K ⟶ (DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F) :
    (LocalCompactSections.functor R G Y).obj K ⟶
      (LocalCompactSections.functor R G X).obj F :=
  (LocalCompactSections.functor R G Y).map b ≫ (natTrans f hf hp).app F

/-- Compact pullback applies precisely the original global component of the sheaf map. -/
@[simp]
theorem pullback_apply (hp : IsProperMap f)
    (b : K ⟶ (DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F)
    (s : Langlands.Sheaf.LocalSupport.submodule (LocalCompactSections.ordinary K.obj)) :
    ((pullback f hf hp b).hom s).val =
      b.hom.app (op ActionOpens.top) s.val := rfl

/-- Varying the source sheaf uses its original compact-section map. -/
theorem pullback_precomp (hp : IsProperMap f)
    {K' : TopologicalSheaf G Y (ModuleCat.{w} R)} (a : K' ⟶ K)
    (b : K ⟶ (DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F) :
    pullback f hf hp (a ≫ b) =
      (LocalCompactSections.functor R G Y).map a ≫ pullback f hf hp b := by
  ext s
  rfl

/-- Varying the target sheaf retains every original equivariant sheaf morphism. -/
theorem pullback_postcomp (hp : IsProperMap f)
    {F' : TopologicalSheaf G X (ModuleCat.{w} R)} (a : F ⟶ F')
    (b : K ⟶ (DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F) :
    pullback f hf hp (b ≫ (DirectImage.sheaf f hf (ModuleCat.{w} R)).map a) =
      pullback f hf hp b ≫ (LocalCompactSections.functor R G X).map a := by
  ext s
  rfl

/-- Arbitrary sheaf maps compose with proper spatial compact pullback. -/
theorem pullback_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    {L : TopologicalSheaf G Z (ModuleCat.{w} R)}
    (b : K ⟶ (DirectImage.sheaf f hf (ModuleCat.{w} R)).obj F)
    (c : L ⟶ (DirectImage.sheaf g hg (ModuleCat.{w} R)).obj K) :
    pullback (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) (c ≫ (DirectImage.sheaf g hg (ModuleCat.{w} R)).map b) =
      pullback g hg hq c ≫ pullback f hf hp b := by
  ext s
  rfl

end Langlands.Sheaf.Equivariant.ProperCompactSections
