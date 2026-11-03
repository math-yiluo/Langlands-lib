import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomBaseChange

/-! # Intrinsic module Hom on Cartesian squares and isomorphic modules -/

noncomputable section

universe v v' u u' u''

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

section Category

variable {C : Type u'} [Category.{v} C] [HasPullbacks C]
variable {B B₀ Y Y₀ : C} {p : Y ⟶ B} {p₀ : Y₀ ⟶ B₀}
    {q : Y ⟶ Y₀} {g : B ⟶ B₀}

/-- A supplied Cartesian square identifies the two base-change functors on
the entire slice over its lower left vertex. -/
def slicePullbackCartesianIso (h : IsPullback q p p₀ g) :
    Over.pullback p ⋙ Over.map q ≅ Over.map g ⋙ Over.pullback p₀ :=
  NatIso.ofComponents
    (fun Z ↦
      let d := ((IsPullback.of_hasPullback Z.hom p).flip.paste_horiz h).flip
      Over.isoMk d.isoPullback d.isoPullback_hom_snd) (by
    intro Z W k
    apply Over.OverMorphism.ext
    change
      pullback.lift (pullback.fst Z.hom p ≫ k.left)
          (pullback.snd Z.hom p) _ ≫
        (((IsPullback.of_hasPullback W.hom p).flip.paste_horiz h).flip).isoPullback.hom =
      (((IsPullback.of_hasPullback Z.hom p).flip.paste_horiz h).flip).isoPullback.hom ≫
        pullback.lift (pullback.fst (Z.hom ≫ g) p₀ ≫ k.left)
          (pullback.snd (Z.hom ≫ g) p₀) _
    apply pullback.hom_ext <;>
      simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
        IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc])

end Category

/-- Isomorphic objects induce naturally isomorphic pseudofunctor Hom
presheaves, by conjugation after every pullback. -/
def presheafHomCongrIso
    {C : Type u'} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u''}) {B : C}
    {M N M' N' : F.obj (.mk (op B))} (eM : M ≅ M') (eN : N ≅ N') :
    F.presheafHom M N ≅ F.presheafHom M' N' :=
  NatIso.ofComponents
    (fun Z ↦ (Iso.homCongr
      ((F.map Z.unop.hom.op.toLoc).toFunctor.mapIso eM)
      ((F.map Z.unop.hom.op.toLoc).toFunctor.mapIso eN)).toIso) (by
    intro Z W k
    ext a
    dsimp [Pseudofunctor.presheafHom, Iso.homCongr, pullHom, Equiv.toIso]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'_hom_naturality_assoc]
    simp only [Pseudofunctor.mapComp'_inv_naturality])

variable {B B₀ Y Y₀ : Scheme.{u}} {p : Y ⟶ B} {p₀ : Y₀ ⟶ B₀}
    {q : Y ⟶ Y₀} {g : B ⟶ B₀}

/-- Intrinsic module Hom commutes with any supplied Cartesian square. -/
def intrinsicModuleHomCartesianIso (h : IsPullback q p p₀ g) (M₀ N₀ : Y₀.Modules) :
    (Over.map g).op ⋙ intrinsicModuleHomPresheaf p₀ M₀ N₀ ≅
      intrinsicModuleHomPresheaf p
        ((Scheme.Modules.pullback q).obj M₀)
        ((Scheme.Modules.pullback q).obj N₀) :=
  (Functor.isoWhiskerRight
    (NatIso.op (slicePullbackCartesianIso h))
    (intrinsicModulePseudofunctor.presheafHom M₀ N₀ ⋙ uliftFunctor.{u + 1})) ≪≫
  Functor.isoWhiskerLeft (Over.pullback p).op
    (Functor.isoWhiskerRight
      (intrinsicModulePseudofunctor.overMapCompPresheafHomIso M₀ N₀ q)
      uliftFunctor.{u + 1})

/-- Intrinsic module Hom is invariant under isomorphisms of both modules. -/
def intrinsicModuleHomCongrIso (p : Y ⟶ B) {M N M' N' : Y.Modules}
    (eM : M ≅ M') (eN : N ≅ N') :
    intrinsicModuleHomPresheaf p M N ≅ intrinsicModuleHomPresheaf p M' N' :=
  Functor.isoWhiskerLeft (Over.pullback p).op
    (Functor.isoWhiskerRight
      (presheafHomCongrIso intrinsicModulePseudofunctor eM eN) uliftFunctor.{u + 1})

/-- A Cartesian model and ordinary module-pullback isomorphisms compare the
actual intrinsic Hom presheaves on every test and restriction map. -/
def intrinsicModuleHomCartesianOfIso
    (h : IsPullback q p p₀ g) {M₀ N₀ : Y₀.Modules} {M N : Y.Modules}
    (eM : (Scheme.Modules.pullback q).obj M₀ ≅ M)
    (eN : (Scheme.Modules.pullback q).obj N₀ ≅ N) :
    (Over.map g).op ⋙ intrinsicModuleHomPresheaf p₀ M₀ N₀ ≅
      intrinsicModuleHomPresheaf p M N :=
  intrinsicModuleHomCartesianIso h M₀ N₀ ≪≫ intrinsicModuleHomCongrIso p eM eN

end Langlands.AlgebraicGeometry.CoherentSheaves
