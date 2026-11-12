import Langlands.AlgebraicGeometry.Modules.FlatBaseChange.AffineCase
import Langlands.AlgebraicGeometry.Modules.FlatBaseChange.OpenImmersionCase
import Langlands.AlgebraicGeometry.Modules.FlatBaseChange.Composition
import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.AlgebraicGeometry.Modules.FlatPullbackExactProof

/-!
# Flat base change of higher direct images: gluing

For a cartesian square `g' ≫ f = f' ≫ g` with `f` quasi-compact and separated and `g` flat, and a
quasi-coherent `M`, every component `(higherDirectImageBaseChangeNatTrans g f f' g' w n).app M` is
an isomorphism. By `isIso_of_affineOpenPullbacks` it suffices to check this after pullback along
affine open immersions `c : Spec T ⟶ Y'` over affine opens `x : Spec R ⟶ Y`; the composition
lemma moves `c` into the square (the open immersion case handles the square of `c`), and then
`c ≫ g = Spec.map φ ≫ x` splits into the open immersion case for `x` and the affine case for
`Spec.map φ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.FlatBaseChange

open Langlands.Cohomology.ExactBaseChange
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution

/-- Pullback along a flat morphism preserves finite limits (the published `flatPullbackExact`). -/
local instance preservesFiniteLimits_pullback_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (Scheme.Modules.pullback f) :=
  flatPullbackExact X Y f inferInstance

/-- Invertibility of a component of the base change transformation only depends on the
morphisms of the square. -/
lemma isIso_higherDirectImageBaseChange_congr {S S' X X' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') {b₁ b₂ : S' ⟶ S} {p₁ p₂ : X' ⟶ X} (w₁ : p₁ ≫ f = f' ≫ b₁)
    (w₂ : p₂ ≫ f = f' ≫ b₂) (hb : b₁ = b₂) (hp : p₁ = p₂)
    [PreservesFiniteLimits (Scheme.Modules.pullback b₁)]
    [PreservesFiniteLimits (Scheme.Modules.pullback p₁)]
    [PreservesFiniteLimits (Scheme.Modules.pullback b₂)]
    [PreservesFiniteLimits (Scheme.Modules.pullback p₂)] (M : X.Modules) (n : ℕ) :
    IsIso ((higherDirectImageBaseChangeNatTrans b₁ f f' p₁ w₁ n).app M) ↔
      IsIso ((higherDirectImageBaseChangeNatTrans b₂ f f' p₂ w₂ n).app M) := by
  subst hb hp
  rfl

/-- A morphism whose composite with an open immersion is flat is flat. -/
lemma flat_of_comp_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion i] (h : Flat (f ≫ i)) : Flat f := by
  refine (Flat.iff_flat_stalkMap f).2 fun x => ?_
  have hx := Flat.stalkMap (f ≫ i) x
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hx
  exact (RingHom.Flat.comp_iff_of_bijective_right
    (ConcreteCategory.bijective_of_isIso (i.stalkMap (f x)))).1 hx

/-- **Gluing.** For a cartesian square `g' ≫ f = f' ≫ g` with `f` quasi-compact and separated and
`g` flat, and a quasi-coherent `M`, the base change transformation of higher direct images is an
isomorphism at `M` in every degree. -/
theorem isIso_higherDirectImageBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [QuasiCompact f] [IsSeparated f] [Flat g] [Flat g']
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((higherDirectImageBaseChangeNatTrans g f f' g' h.w n).app M) := by
  apply isIso_of_affineOpenPullbacks
  intro y
  obtain ⟨R, T, x, c, φ, hx, hc, ⟨t, hty⟩, hw⟩ := exists_affineOpenFactorization g y
  refine ⟨T, c, hc, t, hty, ?_⟩
  -- the square of `c`
  let q : pullback f' c ⟶ X' := pullback.fst f' c
  let fT : pullback f' c ⟶ Spec T := pullback.snd f' c
  have hT : IsPullback q fT f' c := IsPullback.of_hasPullback f' c
  have hB := isIso_higherDirectImageBaseChange_of_isOpenImmersion f' c fT q hT
    ((Scheme.Modules.pullback g').obj M) n
  rw [isIso_pullback_map_higherDirectImageBaseChange_iff g c f f' fT g' q h.w hT.w M n hB]
  -- the square of `x`
  let pR : pullback f x ⟶ X := pullback.fst f x
  let fR : pullback f x ⟶ Spec R := pullback.snd f x
  have hR : IsPullback pR fR f x := IsPullback.of_hasPullback f x
  have wq : (q ≫ g') ≫ f = (fT ≫ Spec.map φ) ≫ x := by
    rw [Category.assoc, h.w, ← Category.assoc, hT.w, Category.assoc, hw, Category.assoc]
  let q' : pullback f' c ⟶ pullback f x := pullback.lift (q ≫ g') (fT ≫ Spec.map φ) wq
  have hq'p : q' ≫ pR = q ≫ g' := pullback.lift_fst _ _ _
  have hq'f : q' ≫ fR = fT ≫ Spec.map φ := pullback.lift_snd _ _ _
  have hout : IsPullback (q' ≫ pR) fT f (Spec.map φ ≫ x) := by
    rw [hq'p, ← hw]
    exact hT.paste_horiz h
  have hq : IsPullback q' fT fR (Spec.map φ) := hout.of_right hq'f hR
  have : Flat (Spec.map φ) := flat_of_comp_isOpenImmersion (Spec.map φ) x (by
    rw [← hw]
    infer_instance)
  have : Flat q' := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact fR := MorphismProperty.of_isPullback hR inferInstance
  have : IsSeparated fR := MorphismProperty.of_isPullback hR inferInstance
  have hS3 := isIso_higherDirectImageBaseChange_affine φ fR fT q' hq
    ((Scheme.Modules.pullback pR).obj M) n
  have hS1 := isIso_higherDirectImageBaseChange_of_isOpenImmersion f x fR pR hR M n
  have hcomp := (isIso_pullback_map_higherDirectImageBaseChange_iff x (Spec.map φ) f fR fT pR q'
    hR.w hq.w M n hS3).1 inferInstance
  exact (isIso_higherDirectImageBaseChange_congr f fT
    (compositeBaseChangeSquare x (Spec.map φ) f fR fT pR q' hR.w hq.w)
    (compositeBaseChangeSquare g c f f' fT g' q h.w hT.w) hw.symm hq'p M n).1 hcomp

end Langlands.AlgebraicGeometry.Modules.FlatBaseChange
