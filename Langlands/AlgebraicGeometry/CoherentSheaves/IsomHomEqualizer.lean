import Langlands.AlgebraicGeometry.CoherentSheaves.HomPresheaf
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# The Isom presheaf as an equalizer of Hom presheaves

For two coherent families `M` and `N`, a point of the actual Isom presheaf is
the same as a pair of maps `a : M ⟶ N` and `b : N ⟶ M` of pulled-back modules
with `a ≫ b = 𝟙` and `b ≫ a = 𝟙`. Hence the Isom presheaf is the equalizer of
the composite map and the identity map from the pointwise product of the two
Hom presheaves to the pointwise product of the two endomorphism presheaves.
-/

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

/-- Coherent restriction in the core pseudofunctor restricts the forward
isomorphism by coherent restriction in the original pseudofunctor. -/
lemma corePseudofunctor_pullHom_iso_hom {C : Type*} [Category* C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {X₁ X₂ Y Y' : C}
    {M₁ : Core (F.obj (.mk (op X₁)))} {M₂ : Core (F.obj (.mk (op X₂)))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : ((corePseudofunctor F).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((corePseudofunctor F).map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (e₁ : g ≫ f₁ = gf₁) (e₂ : g ≫ f₂ = gf₂) :
    (pullHom (F := corePseudofunctor F) φ g gf₁ gf₂ e₁ e₂).iso.hom =
      pullHom (F := F) (M₁ := M₁.of) (M₂ := M₂.of) φ.iso.hom g gf₁ gf₂ e₁ e₂ := by
  subst gf₁ gf₂
  dsimp [pullHom]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- Coherent restriction of a morphism with lifted universe is coherent
restriction of the underlying morphism. -/
lemma homLift_pullHom_down.{w', v, c, v', a} {C : Type c} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', a}) {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : ((Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w'} F).map
        f₁.op.toLoc).toFunctor.obj (ULiftHom.objUp.{a, w'} M₁) ⟶
      ((Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w'} F).map
        f₂.op.toLoc).toFunctor.obj (ULiftHom.objUp.{a, w'} M₂))
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (e₁ : g ≫ f₁ = gf₁) (e₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ e₁ e₂).down = pullHom (F := F) φ.down g gf₁ gf₂ e₁ e₂ := by
  subst gf₁ gf₂
  dsimp [pullHom]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- Restriction in the presheaf of lifted morphisms is restriction of the
underlying morphisms. -/
lemma presheafHom_homLift_map_down.{w', v, c, v', a} {C : Type c} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', a}) {B : C} (M N : F.obj (.mk (op B)))
    {Z Z' : (Over B)ᵒᵖ} (p : Z ⟶ Z')
    (x : ((Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w'} F).presheafHom
      (ULiftHom.objUp.{a, w'} M) (ULiftHom.objUp.{a, w'} N)).obj Z) :
    (((Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w'} F).presheafHom
      (ULiftHom.objUp.{a, w'} M) (ULiftHom.objUp.{a, w'} N)).map p x).down =
      (F.presheafHom M N).map p x.down :=
  homLift_pullHom_down.{w', v, c, v', a} F x p.unop.left Z'.unop.hom Z'.unop.hom p.unop.w p.unop.w

/-- Restriction in the presheaf of core morphisms restricts the forward
isomorphism. -/
lemma presheafHom_corePseudofunctor_map_iso_hom {C : Type*} [Category* C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {B : C} (M N : Core (F.obj (.mk (op B))))
    {Z Z' : (Over B)ᵒᵖ} (p : Z ⟶ Z')
    (x : ((corePseudofunctor F).presheafHom (S := B) M N).obj Z) :
    (((corePseudofunctor F).presheafHom (S := B) M N).map p x).iso.hom =
      (F.presheafHom M.of N.of).map p x.iso.hom :=
  corePseudofunctor_pullHom_iso_hom F x p.unop.left Z'.unop.hom Z'.unop.hom p.unop.w p.unop.w

namespace FamilyGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}

/-- Restricting a point of the Isom presheaf restricts its forward module map. -/
lemma isomPresheaf_map_iso_hom (M N : FamilyGroupoid f T) {Z W : (Over T.left)ᵒᵖ}
    (q : Z ⟶ W) (e : (isomPresheaf f M N).obj Z) :
    ((isomPresheaf f M N).map q e).down.iso.hom =
      ((homPresheaf f M N).map q (ULift.up e.down.iso.hom)).down := by
  have h₁ := presheafHom_homLift_map_down.{u + 1, u, u + 1, u, u + 1} (FamilyGroupoid.pseudofunctor.{u} f) (B := T) M N
    (T.iteratedSliceBackward.op.map q) e
  have h₂ := presheafHom_corePseudofunctor_map_iso_hom (Family.pseudofunctor.{u} f) (B := T) M N
    (T.iteratedSliceBackward.op.map q) e.down
  exact (congrArg (fun x ↦ x.iso.hom) h₁).trans h₂

/-- Restricting a point of the Isom presheaf restricts its inverse module map. -/
lemma isomPresheaf_map_iso_inv (M N : FamilyGroupoid f T) {Z W : (Over T.left)ᵒᵖ}
    (q : Z ⟶ W) (e : (isomPresheaf f M N).obj Z) :
    ((isomPresheaf f M N).map q e).down.iso.inv =
      ((homPresheaf f N M).map q (ULift.up e.down.iso.inv)).down := by
  apply Iso.inv_ext
  rw [isomPresheaf_map_iso_hom]
  have h : homCompose f (ULift.up e.down.iso.hom : (homPresheaf f M N).obj (op Z.unop))
      (ULift.up e.down.iso.inv : (homPresheaf f N M).obj (op Z.unop)) =
      homIdentity f M Z.unop :=
    ULift.ext _ _ e.down.iso.hom_inv_id
  have h' := homPresheaf_map_comp f q.unop
    (ULift.up e.down.iso.hom : (homPresheaf f M N).obj (op Z.unop))
    (ULift.up e.down.iso.inv : (homPresheaf f N M).obj (op Z.unop))
  rw [h, homPresheaf_map_identity] at h'
  exact (congrArg ULift.down h').symm

/-- The forward module map of a point of the Isom presheaf. -/
def isomToHom (M N : FamilyGroupoid f T) : isomPresheaf f M N ⟶ homPresheaf f M N where
  app _ := TypeCat.ofHom fun e ↦ ULift.up e.down.iso.hom
  naturality Z W q := by
    apply ConcreteCategory.hom_ext
    intro e
    apply ULift.ext
    exact isomPresheaf_map_iso_hom f M N q e

/-- The inverse module map of a point of the Isom presheaf. -/
def isomToHomInv (M N : FamilyGroupoid f T) : isomPresheaf f M N ⟶ homPresheaf f N M where
  app _ := TypeCat.ofHom fun e ↦ ULift.up e.down.iso.inv
  naturality Z W q := by
    apply ConcreteCategory.hom_ext
    intro e
    apply ULift.ext
    exact isomPresheaf_map_iso_inv f M N q e

@[simp]
lemma isomToHom_app_down (M N : FamilyGroupoid f T) (Z : (Over T.left)ᵒᵖ)
    (e : (isomPresheaf f M N).obj Z) :
    ((isomToHom f M N).app Z e).down = e.down.iso.hom := rfl

@[simp]
lemma isomToHomInv_app_down (M N : FamilyGroupoid f T) (Z : (Over T.left)ᵒᵖ)
    (e : (isomPresheaf f M N).obj Z) :
    ((isomToHomInv f M N).app Z e).down = e.down.iso.inv := rfl

/-- A point of the Isom presheaf is determined by its forward module map. -/
lemma isomToHom_app_injective (M N : FamilyGroupoid f T) (Z : (Over T.left)ᵒᵖ) :
    Function.Injective ((isomToHom f M N).app Z) := by
  intro e e' h
  apply ULift.ext
  apply Core.hom_ext
  exact congrArg ULift.down h

/-- The two maps `(a, b) ↦ (a ≫ b, b ≫ a)` and `(a, b) ↦ (𝟙, 𝟙)` from pairs of
opposite Hom points to pairs of endomorphism points. -/
def homPairComposites (M N : FamilyGroupoid f T) :
    FunctorToTypes.prod (homPresheaf f M N) (homPresheaf f N M) ⟶
      FunctorToTypes.prod (homPresheaf f M M) (homPresheaf f N N) where
  app _ := TypeCat.ofHom fun x ↦ (homCompose f x.1 x.2, homCompose f x.2 x.1)
  naturality Z W q := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (homPresheaf_map_comp f q.unop x.1 x.2).symm
      (homPresheaf_map_comp f q.unop x.2 x.1).symm

/-- The constant pair of identity endomorphism points. -/
def homPairIdentities (M N : FamilyGroupoid f T) :
    FunctorToTypes.prod (homPresheaf f M N) (homPresheaf f N M) ⟶
      FunctorToTypes.prod (homPresheaf f M M) (homPresheaf f N N) where
  app Z := TypeCat.ofHom fun _ ↦ (homIdentity f M Z.unop, homIdentity f N Z.unop)
  naturality Z W q := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (homPresheaf_map_identity f M q.unop).symm
      (homPresheaf_map_identity f N q.unop).symm

/-- A point of the Isom presheaf gives its forward and inverse module maps. -/
def isomToHomPair (M N : FamilyGroupoid f T) :
    isomPresheaf f M N ⟶ FunctorToTypes.prod (homPresheaf f M N) (homPresheaf f N M) :=
  FunctorToTypes.prod.lift (isomToHom f M N) (isomToHomInv f M N)

lemma isomToHomPair_comp (M N : FamilyGroupoid f T) :
    isomToHomPair f M N ≫ homPairComposites f M N =
      isomToHomPair f M N ≫ homPairIdentities f M N := by
  ext Z e
  · apply ULift.ext
    exact e.down.iso.hom_inv_id
  · apply ULift.ext
    exact e.down.iso.inv_hom_id

/-- The fork exhibiting the Isom presheaf inside pairs of opposite Hom points. -/
def isomPairFork (M N : FamilyGroupoid f T) :
    Fork (homPairComposites f M N) (homPairIdentities f M N) :=
  Fork.ofι (isomToHomPair f M N) (isomToHomPair_comp f M N)

/-- The pair of module maps underlying a point of any fork. -/
private lemma fork_app_comp {M N : FamilyGroupoid f T}
    (s : Fork (homPairComposites f M N) (homPairIdentities f M N))
    (Z : (Over T.left)ᵒᵖ) (x : s.pt.obj Z) :
    ((s.ι.app Z x).1.down ≫ (s.ι.app Z x).2.down = 𝟙 _) ∧
      ((s.ι.app Z x).2.down ≫ (s.ι.app Z x).1.down = 𝟙 _) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app s.condition Z) x
  exact ⟨congrArg (fun y : (homPresheaf f M M).obj Z × (homPresheaf f N N).obj Z ↦ y.1.down) h,
    congrArg (fun y : (homPresheaf f M M).obj Z × (homPresheaf f N N).obj Z ↦ y.2.down) h⟩

/-- The lift of a fork point to an actual isomorphism point. -/
private def forkLiftApp {M N : FamilyGroupoid f T}
    (s : Fork (homPairComposites f M N) (homPairIdentities f M N))
    (Z : (Over T.left)ᵒᵖ) (x : s.pt.obj Z) : (isomPresheaf f M N).obj Z :=
  ULift.up ⟨{
    hom := (s.ι.app Z x).1.down
    inv := (s.ι.app Z x).2.down
    hom_inv_id := (fork_app_comp f s Z x).1
    inv_hom_id := (fork_app_comp f s Z x).2 }⟩

/-- The first component of a map into a product of type-valued functors is natural. -/
private lemma prod_fst_naturality {C : Type*} [Category* C] {P F G : C ⥤ Type w}
    (ι : P ⟶ FunctorToTypes.prod F G) {Z W : C} (q : Z ⟶ W) (x : P.obj Z) :
    (ι.app W (P.map q x)).1 = F.map q (ι.app Z x).1 :=
  congrArg Prod.fst (NatTrans.naturality_apply ι q x)

/-- The forward module map of a fork is natural. -/
private lemma fork_ι_app_fst_naturality {M N : FamilyGroupoid f T}
    (s : Fork (homPairComposites f M N) (homPairIdentities f M N))
    {Z W : (Over T.left)ᵒᵖ} (q : Z ⟶ W) (x : s.pt.obj Z) :
    (s.ι.app W (s.pt.map q x)).1 = (homPresheaf f M N).map q (s.ι.app Z x).1 :=
  prod_fst_naturality (F := homPresheaf f M N) (G := homPresheaf f N M) s.ι q x

/-- The lift of any fork to the Isom presheaf. -/
private def forkLift {M N : FamilyGroupoid f T}
    (s : Fork (homPairComposites f M N) (homPairIdentities f M N)) :
    s.pt ⟶ isomPresheaf f M N where
  app Z := TypeCat.ofHom (forkLiftApp f s Z)
  naturality Z W q := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Core.hom_ext
    exact (congrArg ULift.down (fork_ι_app_fst_naturality f s q x)).trans
      (isomPresheaf_map_iso_hom f M N q (forkLiftApp f s Z x)).symm

private lemma forkLift_ι {M N : FamilyGroupoid f T}
    (s : Fork (homPairComposites f M N) (homPairIdentities f M N)) :
    forkLift f s ≫ (isomPairFork f M N).ι = s.ι := by
  apply NatTrans.ext
  funext Z
  apply ConcreteCategory.hom_ext
  intro x
  rfl

private lemma forkLift_uniq {M N : FamilyGroupoid f T}
    (s : Fork (homPairComposites f M N) (homPairIdentities f M N))
    {m : s.pt ⟶ isomPresheaf f M N} (hm : m ≫ (isomPairFork f M N).ι = s.ι) :
    m = forkLift f s := by
  apply NatTrans.ext
  funext Z
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  apply Core.hom_ext
  exact congrArg (fun y : (homPresheaf f M N).obj Z × (homPresheaf f N M).obj Z ↦ y.1.down)
    (ConcreteCategory.congr_hom (NatTrans.congr_app hm Z) x)

/-- The Isom presheaf is the equalizer of the composite and identity maps. -/
def isomPairForkIsLimit (M N : FamilyGroupoid f T) : IsLimit (isomPairFork f M N) :=
  Fork.IsLimit.mk' _ fun s ↦ ⟨forkLift f s, forkLift_ι f s, forkLift_uniq f s⟩

end FamilyGroupoid

end Langlands.AlgebraicGeometry.CoherentSheaves
