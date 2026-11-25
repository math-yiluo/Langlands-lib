/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalBaseChangeOpenRestriction
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-! # Descent of exceptional base change from affine base charts

Source: blueprint `proposition-exceptional-inverse-image-smooth-morphism--6`, coherences (i) and
(iii).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

/-- Locality on the base of invertibility of the exceptional base-change mate.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism--6, proof, restriction to
base charts and descent. For each affine open of the base, suppose the restricted morphism satisfies
arbitrary base change. Then the original morphism satisfies base change. Restrict a chosen
compactification and its proper/open exchange to the affine cover, use horizontal pasting of
exchange maps, and take mates. The restrictions of the original mate differ from the local mates by
invertible open-restriction comparisons. The inverse images of the affine opens cover the
base-changed source, so their exact inverse-image functors jointly detect isomorphisms.
(blueprint: lem-asd-exceptional-base-change-affine-locality) -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_affine_open
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (h : ∀ {U V : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [IsAffine U]
      {a : V ⟶ X} {p : V ⟶ U} (_sqU : IsPullback a p f j) [HasCompactification p]
      {V' U' : Scheme.{u}} {b : V' ⟶ V} {p' : V' ⟶ U'} {c : U' ⟶ U}
      (sq' : IsPullback b p' p c) [HasCompactification p'] [QuasiCompact p'],
      IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq')) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  let j := Y.affineCover.f
  let U := Y.affineCover.X
  let V (i : Y.affineCover.I₀) := pullback f (j i)
  let a (i : Y.affineCover.I₀) : V i ⟶ X := pullback.fst f (j i)
  let p (i : Y.affineCover.I₀) : V i ⟶ U i := pullback.snd f (j i)
  let sqU (i : Y.affineCover.I₀) : IsPullback (a i) (p i) f (j i) :=
    IsPullback.of_hasPullback _ _
  let U' (i : Y.affineCover.I₀) := pullback (j i) g
  let c (i : Y.affineCover.I₀) : U' i ⟶ U i := pullback.fst (j i) g
  let j' (i : Y.affineCover.I₀) : U' i ⟶ Y' := pullback.snd (j i) g
  let sqj (i : Y.affineCover.I₀) : IsPullback (c i) (j' i) (j i) g :=
    IsPullback.of_hasPullback _ _
  let V' (i : Y.affineCover.I₀) := pullback f' (j' i)
  let a' (i : Y.affineCover.I₀) : V' i ⟶ X' := pullback.fst f' (j' i)
  let p' (i : Y.affineCover.I₀) : V' i ⟶ U' i := pullback.snd f' (j' i)
  let sqV (i : Y.affineCover.I₀) : IsPullback (a' i) (p' i) f' (j' i) :=
    IsPullback.of_hasPullback _ _
  have heq (i : Y.affineCover.I₀) :
      (a' i ≫ g') ≫ f = (p' i ≫ c i) ≫ j i := by
    rw [Category.assoc, sq.w, ← Category.assoc, (sqV i).w, Category.assoc,
      ← (sqj i).w, ← Category.assoc]
  let b (i : Y.affineCover.I₀) : V' i ⟶ V i :=
    (sqU i).lift (a' i ≫ g') (p' i ≫ c i) (heq i)
  have hb (i : Y.affineCover.I₀) : b i ≫ a i = a' i ≫ g' := (sqU i).lift_fst _ _ _
  have sq' (i : Y.affineCover.I₀) : IsPullback (b i) (p' i) (p i) (c i) := by
    apply IsPullback.of_right _ ((sqU i).lift_snd _ _ _) (sqU i)
    rw [hb i, (sqj i).w]
    exact (sqV i).paste_horiz sq
  have (i : Y.affineCover.I₀) : HasCompactification (p i) := .of_isPullback (sqU i)
  have (i : Y.affineCover.I₀) : HasCompactification (p' i) := .of_isPullback (sqV i)
  have (i : Y.affineCover.I₀) : QuasiCompact (p' i) :=
    MorphismProperty.of_isPullback (sqV i) inferInstance
  have hcover : ∀ x : X', ∃ (i : Y.affineCover.I₀) (y : V' i), (a' i).base y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := Y.affineCover.exists_eq (g.base (f'.base x))
    have hx : x ∈ Set.range (a' i).base := by
      change x ∈ Set.range (pullback.fst f' (pullback.snd (j i) g)).base
      rw [IsOpenImmersion.range_pullbackFst]
      change f'.base x ∈ Set.range (pullback.snd (j i) g).base
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hx
    exact ⟨i, z, hz⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  apply isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ a' hcover
  intro i
  apply isIso_leftDerivedUpperStar_map_baseChange_of_open_restriction
    Λ sq (sqU i) (sqj i) (sq' i) (sqV i) (hb i) K
  have := h (j i) (sqU i) (sq' i)
  infer_instance

end AlgebraicGeometry.Etale
