import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of the full Weil restriction presheaf

For a cartesian square of schemes, restriction of scalars and base change
commute on all test schemes. The comparison comes from pasting pullback
squares, before any representability assertion.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace WeilRestrictionBaseChange

variable {S S' T T' : Scheme.{u}}
variable {g : S' ⟶ S} {f : T ⟶ S} {f' : T' ⟶ S'} {g' : T' ⟶ T}
variable (h : IsPullback f' g' g f)

include h

/-- Pasting the test-scheme pullback with the given base-change square. -/
theorem testPullback (U : Over T) :
    IsPullback (pullback.fst U.hom g') (pullback.snd U.hom g' ≫ f') (U.hom ≫ f) g :=
  (IsPullback.of_hasPullback U.hom g').paste_vert h.flip

/-- The two base-changed test schemes, viewed over the original upper base. -/
def testIso (U : Over T) :
    (Over.map f').obj ((Over.pullback g').obj U) ≅
      (Over.pullback g).obj ((Over.map f).obj U) :=
  Over.isoMk (testPullback h U).isoPullback (by
    exact (testPullback h U).isoPullback_hom_snd)

@[reassoc (attr := simp)]
theorem testIso_hom_fst (U : Over T) :
    (testIso h U).hom.left ≫ pullback.fst (U.hom ≫ f) g = pullback.fst U.hom g' :=
  (testPullback h U).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem testIso_hom_snd (U : Over T) :
    (testIso h U).hom.left ≫ pullback.snd (U.hom ≫ f) g =
      pullback.snd U.hom g' ≫ f' :=
  (testPullback h U).isoPullback_hom_snd

/-- Naturality of the comparison in every test scheme over the new lower base. -/
def testNatIso :
    Over.pullback g' ⋙ Over.map f' ≅ Over.map f ⋙ Over.pullback g :=
  NatIso.ofComponents (testIso h) (by
    intro U V a
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc])

end WeilRestrictionBaseChange

variable {S S' T T' : Scheme.{u}}
variable {g : S' ⟶ S} {f : T ⟶ S} {f' : T' ⟶ S'} {g' : T' ⟶ T}

/-- Base change commutes with the full Weil restriction presheaf along a cartesian
square. This is a natural isomorphism on all test schemes, with no finiteness assumptions. -/
def weilRestrictionBaseChangePresheafIso (h : IsPullback f' g' g f) (P : Presheaf S') :
    (Over.map f).op ⋙ (Over.pullback g).op ⋙ P ≅
      (Over.pullback g').op ⋙ (Over.map f').op ⋙ P :=
  isoWhiskerRight (NatIso.op (WeilRestrictionBaseChange.testNatIso h)) P

/-- The component map is pullback along the canonical comparison of test schemes. -/
theorem weilRestrictionBaseChangePresheafIso_hom_app
    (h : IsPullback f' g' g f) (P : Presheaf S') (U : Over T) :
    (weilRestrictionBaseChangePresheafIso h P).hom.app (op U) =
      P.map (WeilRestrictionBaseChange.testIso h U).hom.op :=
  rfl

/-- When the two restrictions are algebraic spaces, the full presheaf comparison
identifies the base change of one restriction with the restriction of the base change. -/
def weilRestrictionBaseChangeSpaceIso (h : IsPullback f' g' g f)
    (X' : AlgebraicSpace S')
    (hX : IsAlgebraicSpace S ((weilRestriction g).obj X'.toSheaf))
    (hXT : IsAlgebraicSpace T
      ((weilRestriction g').obj (baseChange f' X').toSheaf)) :
    baseChange f ⟨(weilRestriction g).obj X'.toSheaf, hX⟩ ≅
      (⟨(weilRestriction g').obj (baseChange f' X').toSheaf, hXT⟩ : AlgebraicSpace T) where
  hom := homMk (weilRestrictionBaseChangePresheafIso h X'.presheaf).hom
  inv := homMk (weilRestrictionBaseChangePresheafIso h X'.presheaf).inv
  hom_inv_id := (homEquiv _ _).injective
    (weilRestrictionBaseChangePresheafIso h X'.presheaf).hom_inv_id
  inv_hom_id := (homEquiv _ _).injective
    (weilRestrictionBaseChangePresheafIso h X'.presheaf).inv_hom_id

end Langlands.AlgebraicGeometry.AlgebraicSpace
