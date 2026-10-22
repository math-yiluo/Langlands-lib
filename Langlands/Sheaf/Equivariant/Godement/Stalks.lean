import Langlands.Sheaf.Equivariant.Topological
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalk transport for equivariant presheaves

The maps are induced from the actual neighborhood colimits defining Mathlib
stalks. A label carrying `x` to `y` induces a contravariant map from the stalk
at `y` to the stalk at `x`.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u uG uA

variable {G : Type uG} [Group G] {X : Type u} [TopologicalSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]
variable {A : Type uA} [Category.{u} A] [HasColimits.{u} A]

/-- The inverse image of an open under a group operator. -/
def preimageOpen (g : G) (U : Opens X) : Opens X :=
  ⟨{x | g • x ∈ U}, U.isOpen.preimage (continuous_const_smul g)⟩

/-- The group-labelled arrow from an inverse image open to the given open. -/
def preimageArrow (g : G) (U : Opens X) :
    (⟨preimageOpen g U⟩ : ActionOpens G X) ⟶ ⟨U⟩ :=
  ⟨g, fun _ hx => hx⟩

/-- The cocone of translated germs, with vertex the stalk at the source point. -/
def stalkPullCocone (F : (ActionOpens G X)ᵒᵖ ⥤ A)
    (g : G) (x y : X) (h : g • x = y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ (underlyingPresheaf G X A).obj F) where
  pt := ((underlyingPresheaf G X A).obj F).stalk x
  ι :=
    { app U := F.map (preimageArrow g U.unop.1).op ≫
        ((underlyingPresheaf G X A).obj F).germ (preimageOpen g U.unop.1) x (by
          change g • x ∈ U.unop.1
          rw [h]
          exact U.unop.2)
      naturality U V f := by
        dsimp
        rw [Category.comp_id]
        let i : preimageOpen g V.unop.1 ⟶ preimageOpen g U.unop.1 :=
          homOfLE (fun _ hx => f.unop.le hx)
        have arrows :
            preimageArrow g V.unop.1 ≫
                (ActionOpens.inclusion G X).map f.unop =
              (ActionOpens.inclusion G X).map i ≫
                preimageArrow g U.unop.1 := by
          apply ActionOpens.Hom.ext
          simp [preimageArrow, ActionOpens.inclusion]
        change F.map ((ActionOpens.inclusion G X).map f.unop).op ≫
            F.map (preimageArrow g V.unop.1).op ≫
              ((underlyingPresheaf G X A).obj F).germ (preimageOpen g V.unop.1) x _ =
          F.map (preimageArrow g U.unop.1).op ≫
            ((underlyingPresheaf G X A).obj F).germ (preimageOpen g U.unop.1) x _
        rw [← F.map_comp_assoc]
        have arrowop := congrArg Quiver.Hom.op arrows
        rw [op_comp, op_comp] at arrowop
        rw [arrowop, F.map_comp, Category.assoc]
        congr 1
        exact ((underlyingPresheaf G X A).obj F).germ_res i x _ }

/-- Pull a germ back along a group-labelled point map, using its colimit. -/
def stalkPull (F : (ActionOpens G X)ᵒᵖ ⥤ A)
    (g : G) (x y : X) (h : g • x = y) :
    ((underlyingPresheaf G X A).obj F).stalk y ⟶ ((underlyingPresheaf G X A).obj F).stalk x :=
  colimit.desc _ (stalkPullCocone F g x y h)

@[reassoc]
theorem germ_stalkPull (F : (ActionOpens G X)ᵒᵖ ⥤ A)
    (g : G) (x y : X) (h : g • x = y) (U : Opens X) (hy : y ∈ U) :
    ((underlyingPresheaf G X A).obj F).germ U y hy ≫ stalkPull F g x y h =
      F.map (preimageArrow g U).op ≫
        ((underlyingPresheaf G X A).obj F).germ (preimageOpen g U) x (by
          change g • x ∈ U
          rw [h]
          exact hy) :=
  colimit.ι_desc _ _

/-- Germ transport agrees with every actual labelled restriction arrow. -/
@[reassoc]
theorem germ_stalkPull_arrow (F : (ActionOpens G X)ᵒᵖ ⥤ A)
    {U V : ActionOpens G X} (f : U ⟶ V)
    (x y : X) (h : f.label • x = y) (hx : x ∈ U.openSet) :
    ((underlyingPresheaf G X A).obj F).germ V.openSet y (h ▸ f.mapsTo x hx) ≫
        stalkPull F f.label x y h =
      F.map f.op ≫ ((underlyingPresheaf G X A).obj F).germ U.openSet x hx := by
  rw [germ_stalkPull]
  let i : U.openSet ⟶ preimageOpen f.label V.openSet :=
    homOfLE f.mapsTo
  rw [← ((underlyingPresheaf G X A).obj F).germ_res i x hx]
  rw [← Category.assoc]
  change (F.map (preimageArrow f.label V.openSet).op ≫
    F.map ((ActionOpens.inclusion G X).map i).op) ≫ _ = _
  rw [← F.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply ActionOpens.Hom.ext
  simp [preimageArrow, ActionOpens.inclusion]

@[simp]
theorem stalkPull_one (F : (ActionOpens G X)ᵒᵖ ⥤ A) (x : X)
    (h : (1 : G) • x = x) :
    stalkPull F 1 x x h = 𝟙 _ := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  simpa using germ_stalkPull_arrow F (𝟙 (⟨U⟩ : ActionOpens G X)) x x h hx

/-- Composition reverses group-labelled point maps, as it does on sections. -/
theorem stalkPull_mul (F : (ActionOpens G X)ᵒᵖ ⥤ A)
    (g k : G) (x y z : X) (hg : g • x = y) (hk : k • y = z) :
    stalkPull F (k * g) x z (by rw [mul_smul, hg, hk]) =
      stalkPull F k y z hk ≫ stalkPull F g x y hg := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hz
  let V := preimageOpen k U
  let W := preimageOpen g V
  have hy : y ∈ V := by change k • y ∈ U; rw [hk]; exact hz
  have hx : x ∈ W := by change g • x ∈ V; rw [hg]; exact hy
  have hm : (k * g) • x = z := by rw [mul_smul, hg, hk]
  have step := germ_stalkPull_arrow F
    (preimageArrow g V ≫ preimageArrow k U) x z hm hx
  conv_rhs => rw [germ_stalkPull_assoc, germ_stalkPull]
  simpa only [ActionOpens.comp_label, preimageArrow, op_comp,
    F.map_comp, Category.assoc, V] using step

/-- Stalk transport is natural in equivariant presheaf morphisms. -/
@[reassoc]
theorem stalkPull_naturality {F F' : (ActionOpens G X)ᵒᵖ ⥤ A}
    (f : F ⟶ F') (g : G) (x y : X) (h : g • x = y) :
    stalkPull F g x y h ≫
        (TopCat.Presheaf.stalkFunctor A x).map
          ((underlyingPresheaf G X A).map f) =
      (TopCat.Presheaf.stalkFunctor A y).map
          ((underlyingPresheaf G X A).map f) ≫
        stalkPull F' g x y h := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hy
  rw [germ_stalkPull_assoc, TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  change F.map (preimageArrow g U).op ≫
      f.app (op ⟨preimageOpen g U⟩) ≫ ((underlyingPresheaf G X A).obj F').germ _ x _ =
    f.app (op ⟨U⟩) ≫ ((underlyingPresheaf G X A).obj F').germ U y hy ≫
      stalkPull F' g x y h
  rw [germ_stalkPull]
  exact f.naturality_assoc _ _

/-- Group inverses give inverse maps on the actual stalks. -/
def stalkPullIso (F : (ActionOpens G X)ᵒᵖ ⥤ A)
    (g : G) (x y : X) (h : g • x = y) :
    ((underlyingPresheaf G X A).obj F).stalk y ≅ ((underlyingPresheaf G X A).obj F).stalk x where
  hom := stalkPull F g x y h
  inv := stalkPull F g⁻¹ y x (by rw [← h, inv_smul_smul])
  hom_inv_id := by
    rw [← stalkPull_mul]
    simp only [mul_inv_cancel, stalkPull_one]
  inv_hom_id := by
    rw [← stalkPull_mul]
    simp only [inv_mul_cancel, stalkPull_one]

end Langlands.Sheaf.Equivariant.Godement
