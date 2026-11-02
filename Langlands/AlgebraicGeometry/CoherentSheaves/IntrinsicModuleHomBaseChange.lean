import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf

/-! # Arbitrary base change of intrinsic module Hom presheaves -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

section Category

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {B B' Y : C} (p : Y ⟶ B) (g : B' ⟶ B)

/-- The two iterated base changes of a test over `B'` are canonically
isomorphic over `Y`, naturally on the entire slice. -/
def slicePullbackBaseChangeIso :
    Over.pullback (pullback.fst g p) ⋙ Over.map (pullback.snd g p) ≅
      Over.map g ⋙ Over.pullback p :=
  NatIso.ofComponents
    (fun Z ↦
      let h := ((IsPullback.of_hasPullback Z.hom (pullback.fst g p)).flip.paste_horiz
        (IsPullback.of_hasPullback g p).flip).flip
      Over.isoMk h.isoPullback h.isoPullback_hom_snd) (by
    intro Z W k
    apply Over.OverMorphism.ext
    change
      pullback.lift
          (pullback.fst Z.hom (pullback.fst g p) ≫ k.left)
          (pullback.snd Z.hom (pullback.fst g p)) _ ≫
        (((IsPullback.of_hasPullback W.hom (pullback.fst g p)).flip.paste_horiz
          (IsPullback.of_hasPullback g p).flip).flip).isoPullback.hom =
      (((IsPullback.of_hasPullback Z.hom (pullback.fst g p)).flip.paste_horiz
          (IsPullback.of_hasPullback g p).flip).flip).isoPullback.hom ≫
        pullback.lift
          (pullback.fst (Z.hom ≫ g) p ≫ k.left)
          (pullback.snd (Z.hom ≫ g) p) _
    apply pullback.hom_ext <;>
      simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
        IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc])

end Category

variable {B B' Y : Scheme.{u}} (p : Y ⟶ B) (g : B' ⟶ B)
    (M N : Y.Modules)

/-- Intrinsic ordinary-module Hom commutes with restriction along any base
change, with its full-slice naturality and explicit value lift. -/
def intrinsicModuleHomBaseChangeIso :
    (Over.map g).op ⋙ intrinsicModuleHomPresheaf p M N ≅
      intrinsicModuleHomPresheaf (pullback.fst g p)
        ((Scheme.Modules.pullback (pullback.snd g p)).obj M)
        ((Scheme.Modules.pullback (pullback.snd g p)).obj N) :=
  (Functor.isoWhiskerRight
    (NatIso.op (slicePullbackBaseChangeIso p g))
    (intrinsicModulePseudofunctor.presheafHom M N ⋙ uliftFunctor.{u + 1})) ≪≫
  Functor.isoWhiskerLeft (Over.pullback (pullback.fst g p)).op
    (Functor.isoWhiskerRight
      (intrinsicModulePseudofunctor.overMapCompPresheafHomIso M N (pullback.snd g p))
      uliftFunctor.{u + 1})

end Langlands.AlgebraicGeometry.CoherentSheaves
