import Langlands.AlgebraicGeometry.CoherentSheaves.ModuleHomPresheaf

/-! # Intrinsic relative module Hom presheaves -/

noncomputable section

universe v v' w u u' u''

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

/-- Module pullback as a Cat-valued pseudofunctor. -/
abbrev intrinsicModulePseudofunctor :
    LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

/-- All module maps after arbitrary base change of a fixed scheme morphism. -/
def intrinsicModuleHomPresheaf {B Y : Scheme.{u}} (p : Y ⟶ B)
    (M N : Y.Modules) : AlgebraicSpace.Presheaf B :=
  (Over.pullback p).op ⋙
    ((intrinsicModulePseudofunctor).presheafHom M N ⋙ uliftFunctor.{u + 1})

/-- Its values are all maps of ordinary module pullbacks, with the explicit lift. -/
def intrinsicModuleHomPointsEquiv {B Y : Scheme.{u}} (p : Y ⟶ B)
    (M N : Y.Modules) (Z : Over B) :
    (intrinsicModuleHomPresheaf p M N).obj (op Z) ≃
      ULift.{u + 1}
        ((Scheme.Modules.pullback (pullback.snd Z.hom p)).obj M ⟶
          (Scheme.Modules.pullback (pullback.snd Z.hom p)).obj N) :=
  Equiv.refl _

private lemma precomp_pullHom
    {C : Type u'} [Category.{v} C] {D : Type u''} [Category.{w} D]
    (G : C ⥤ D) (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v', u})
    {B : C} {M N : F.obj (.mk (op (G.obj B)))}
    {Z W : Over B}
    (a : ((G.op.toPseudofunctor.comp F).presheafHom M N).obj (op Z))
    (q : W ⟶ Z) :
    pullHom (F := G.op.toPseudofunctor.comp F) a q.left W.hom W.hom =
      pullHom (F := F) a (G.map q.left) (G.map W.hom) (G.map W.hom)
        (by simp [← G.map_comp]) (by simp [← G.map_comp]) := by
  dsimp [pullHom, Pseudofunctor.mapComp', Pseudofunctor.comp]
  simp [Quiver.Hom.toLoc, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_trans]
  rfl

/-- Reindexing a pseudofunctor commutes with the presheaf of all morphisms. -/
def precompPresheafHomIso
    {C : Type u'} [Category.{v} C] {D : Type u''} [Category.{w} D]
    (G : C ⥤ D) (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v', u})
    {B : C} (M N : F.obj (.mk (op (G.obj B)))) :
    (G.op.toPseudofunctor.comp F).presheafHom M N ≅
      (Over.post G).op ⋙ F.presheafHom M N :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Z W q
    apply ConcreteCategory.hom_ext
    intro a
    exact precomp_pullHom G F a q.unop)

/-- Reassociation of pseudofunctor composition preserves the presheaf of all
morphisms, by the identity on its values. -/
def compAssocPresheafHomIso
    {A : Type*} [Category A] {B C : Type*} [Bicategory B] [Bicategory C]
    (F : LocallyDiscrete Aᵒᵖ ⥤ᵖ B) (G : B ⥤ᵖ C) (H : C ⥤ᵖ Cat.{v', u'})
    {Z : A} (M N : H.obj (G.obj (F.obj (.mk (op Z))))) :
    ((F.comp G).comp H).presheafHom M N ≅
      (F.comp (G.comp H)).presheafHom M N :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Z W q
    apply ConcreteCategory.hom_ext
    intro a
    dsimp [Pseudofunctor.presheafHom, pullHom, Pseudofunctor.mapComp',
      Pseudofunctor.comp]
    simp [PrelaxFunctor.map₂_comp, Category.assoc]
    rfl)

variable {S X : Scheme.{u}} (f : X ⟶ S) (T : Over S)

/-- The actual relative spaces over tests of `T` are the base changes of the
fixed relative projection, naturally on the entire slice over `T.left`. -/
def relativeSpaceSlicePullbackIso :
    T.iteratedSliceBackward ⋙ Over.post (Picard.relativeSpace f) ≅
      Over.pullback ((Picard.relativeProjection f).app T) :=
  NatIso.ofComponents
    (fun Z ↦ Over.isoMk
      (Picard.relativeProjection_isPullback f (FamilyGroupoid.testMap T Z)).flip.isoPullback
      (Picard.relativeProjection_isPullback f
        (FamilyGroupoid.testMap T Z)).flip.isoPullback_hom_snd) (by
    intro Z W q
    apply Over.OverMorphism.ext
    change
      (Picard.relativeSpace f).map ((Over.map T.hom).map q) ≫
          (Picard.relativeProjection_isPullback f
            (FamilyGroupoid.testMap T W)).flip.isoPullback.hom =
        (Picard.relativeProjection_isPullback f
          (FamilyGroupoid.testMap T Z)).flip.isoPullback.hom ≫
            pullback.lift (pullback.fst _ _ ≫ q.left) (pullback.snd _ _) _
    apply pullback.hom_ext
    · simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
        pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
      exact (Picard.relativeProjection f).naturality
        ((Over.map T.hom).map q)
    · simp only [Category.assoc, IsPullback.isoPullback_hom_snd,
        pullback.lift_snd]
      exact ((Picard.relativeSpace f).map_comp
        ((Over.map T.hom).map q) (FamilyGroupoid.testMap T W)).symm.trans
          (congrArg (Picard.relativeSpace f).map
            ((T.iteratedSliceBackward.map q).w)))

/-- Reassociation of the underlying module pseudofunctor leaves its Hom
presheaf unchanged up to the identity on each actual module map. -/
def modulePseudofunctorHomIso
    (M N : ((Picard.relativeSpace f).obj T).Modules) :
    (modulePseudofunctor f).presheafHom M N ≅
      ((Picard.relativeSpace f).op.toPseudofunctor.comp
        intrinsicModulePseudofunctor).presheafHom M N :=
  compAssocPresheafHomIso (Picard.relativeSpace f).op.toPseudofunctor
    Scheme.Modules.pseudofunctor Adj.forget₁ M N

/-- The original relative-space Hom presheaf is the intrinsic ordinary-module
Hom presheaf of the fixed relative projection, naturally on every test scheme. -/
def moduleHomPresheafIntrinsicIso
    (M N : ((Picard.relativeSpace f).obj T).Modules) :
    moduleHomPresheaf f M N ≅
      intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T) M N :=
  (Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (Functor.isoWhiskerRight (modulePseudofunctorHomIso f T M N)
      uliftFunctor.{u + 1})) ≪≫
    (Functor.isoWhiskerLeft T.iteratedSliceBackward.op
      (Functor.isoWhiskerRight
        (precompPresheafHomIso (Picard.relativeSpace f)
          intrinsicModulePseudofunctor M N) uliftFunctor.{u + 1})) ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (relativeSpaceSlicePullbackIso f T)).symm
      (intrinsicModulePseudofunctor.presheafHom M N ⋙ uliftFunctor.{u + 1})

namespace FamilyGroupoid

/-- All actual coherent-family maps agree, on the entire slice, with all
ordinary pulled-back module maps for the fixed relative projection. -/
def homPresheafIntrinsicIso (M N : FamilyGroupoid f T) :
    homPresheaf f M N ≅
      intrinsicModuleHomPresheaf ((Picard.relativeProjection f).app T)
        M.of.obj N.of.obj :=
  homPresheafModuleIso f M N ≪≫
    moduleHomPresheafIntrinsicIso f T M.of.obj N.of.obj

end FamilyGroupoid

end Langlands.AlgebraicGeometry.CoherentSheaves
