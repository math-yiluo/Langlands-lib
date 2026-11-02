import Langlands.Sheaf.Equivariant.Godement.Zero
import Langlands.Sheaf.Equivariant.DirectImage

/-! # Spatial maps on equivariant stalk families -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement.Spatial

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The genuine neighborhood-colimit map from a direct-image stalk. -/
def stalkMap (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) (x : X) :
    ((underlyingPresheaf G Y (ModuleCat.{u} R)).obj
        ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F)).stalk (f x) ⟶
      ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x :=
  TopCat.Presheaf.stalkPushforward (ModuleCat.{u} R) (TopCat.ofHom f)
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F) x

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
@[reassoc (attr := simp)]
theorem germ_stalkMap (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (U : Opens Y) (x : X) (hx : f x ∈ U) :
    ((underlyingPresheaf G Y (ModuleCat.{u} R)).obj
        ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F)).germ U (f x) hx ≫
        stalkMap f hf F x =
      ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).germ
        ((Opens.map (TopCat.ofHom f)).obj U) x hx :=
  TopCat.Presheaf.stalkPushforward_germ (ModuleCat.{u} R) (TopCat.ofHom f)
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F) U x hx

/-- Spatial stalk maps commute with every actual group transport. -/
@[reassoc]
theorem stalkMap_transport (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (g : G) (x y : X) (h : g • x = y) :
    stalkPull ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F)
        g (f x) (f y) (by rw [← hf, h]) ≫ stalkMap f hf F x =
      stalkMap f hf F y ≫ stalkPull F g x y h := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hy
  rw [germ_stalkPull_assoc, germ_stalkMap, germ_stalkMap_assoc]
  exact (germ_stalkPull_arrow F
    ((DirectImage.preimage f hf).map (preimageArrow g U))
    x y h (by change g • f x ∈ U; rw [← hf, h]; exact hy)).symm

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
/-- The stalk map is natural in every original presheaf morphism. -/
@[reassoc]
theorem stalkMap_naturality {F F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (a : F ⟶ F') (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) (f x)).map
        ((underlyingPresheaf G Y (ModuleCat.{u} R)).map
          ((DirectImage.presheaf f hf (ModuleCat.{u} R)).map a)) ≫
        stalkMap f hf F' x =
      stalkMap f hf F x ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
          ((underlyingPresheaf G X (ModuleCat.{u} R)).map a) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, germ_stalkMap,
    germ_stalkMap_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

omit [ContinuousConstSMul G X] in
@[simp]
theorem stalkMap_id (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) (x : X) :
    stalkMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F x = 𝟙 _ := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [germ_stalkMap, Category.comp_id]
  rfl

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z] in
/-- Spatial composition retains the actual two neighborhood-colimit maps. -/
theorem stalkMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) (x : X) :
    stalkMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F x =
      stalkMap g hg ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F) (f x) ≫
        stalkMap f hf F x :=
  TopCat.Presheaf.stalkPushforward.comp (ModuleCat.{u} R)
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F)
    (TopCat.ofHom f) (TopCat.ofHom g) x

/-- A pointwise version retaining both presentations of the translated image. -/
theorem stalkMap_transport_section
    (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (g : G) (x y : X) (h : g • x = y) (z : Y)
    (hz : z = f y) (hg : g • f x = z) (U : Opens Y)
    (s : ∀ t : U, ((underlyingPresheaf G Y (ModuleCat.{u} R)).obj
      ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F)).stalk t.1)
    (hzu : z ∈ U) (hyu : f y ∈ U) :
    stalkMap f hf F x
        (stalkPull ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F)
          g (f x) z hg (s ⟨z, hzu⟩)) =
      stalkPull F g x y h (stalkMap f hf F y (s ⟨f y, hyu⟩)) := by
  subst z
  exact congrArg (fun a => a (s ⟨f y, hyu⟩))
    (stalkMap_transport f hf F g x y h)

/-- Pull a family at `f(x)` back to the original stalk at `x`. -/
def zeroMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (zeroFunctor R G Y).obj ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ⟶
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj ((zeroFunctor R G X).obj F) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun s x := stalkMap f hf F.obj x.1 (s ⟨f x.1, x.2⟩)
          map_add' s t := by ext x; exact map_add _ _ _
          map_smul' r s := by ext x; exact map_smul _ _ _ }
      naturality U V k := by
        ext s
        funext x
        exact stalkMap_transport_section f hf F.obj k.unop.label x.1
          (k.unop.label • x.1) rfl (k.unop.label • f x.1)
          (hf _ _).symm rfl U.unop.openSet s _ _ }

@[simp]
theorem zeroMap_apply (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G Y) (s : StalkSections
      ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F).obj U)
    (x : ((DirectImage.preimage f hf).obj U).openSet) :
    ((zeroMap f hf F).hom.app (op U) s) x =
      stalkMap f hf F.obj x.1 (s ⟨f x.1, x.2⟩) := rfl

/-- The degree-zero spatial comparison is natural in the full sheaf category. -/
def zeroNatTrans :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ zeroFunctor R G Y ⟶
      zeroFunctor R G X ⋙ DirectImage.sheaf f hf (ModuleCat.{u} R) where
  app F := zeroMap f hf F
  naturality F F' a := by
    apply ObjectProperty.hom_ext
    ext U s
    funext x
    exact congrArg (fun b => b (s ⟨f x.1, x.2⟩))
      (stalkMap_naturality f hf a.hom x.1)

/-- The spatial comparison carries the actual family of germs to that on `X`. -/
@[reassoc]
theorem coaugmentation_zeroMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (coaugmentation R G Y).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        zeroMap f hf F =
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) := by
  apply ObjectProperty.hom_ext
  ext U s
  funext x
  exact congrArg (fun b => b s) (germ_stalkMap f hf F.obj U.unop.openSet x.1 x.2)

@[simp]
theorem zeroMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    zeroMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      𝟙 ((zeroFunctor R G X).obj F) := by
  apply ObjectProperty.hom_ext
  ext U s
  funext x
  change stalkMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F.obj x.1
    (s ⟨x.1, x.2⟩) = s x
  rw [stalkMap_id]
  rfl

/-- The degree-zero comparison is compatible with spatial composition. -/
theorem zeroMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    zeroMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      zeroMap g hg ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (DirectImage.sheaf g hg (ModuleCat.{u} R)).map (zeroMap f hf F) := by
  apply ObjectProperty.hom_ext
  ext U s
  funext x
  exact congrArg (fun b => b (s ⟨g (f x.1), x.2⟩))
    (stalkMap_comp f hf g hg F.obj x.1)

end Langlands.Sheaf.Equivariant.Godement.Spatial
