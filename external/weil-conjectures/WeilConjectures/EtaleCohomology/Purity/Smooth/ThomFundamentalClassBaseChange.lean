/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomFramesFundamentalClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapBaseChange

/-!
# Base change of the fundamental class of a closed immersion with Thom frames

Let `i : Z ⟶ X` be a closed immersion with Thom frames and regular Zariski frames
(`AlgebraicGeometry.Etale.HasThomFrames`, `AlgebraicGeometry.Etale.HasRegularZariskiFrames`),
and let `i' : Z' ⟶ X'` be its base change along any `e : X' ⟶ X`, again with such frames. Then the
restriction of supports along `e` carries the fundamental class `[Z ⊂ X]`
(`AlgebraicGeometry.Etale.thomFundamentalClass`) to `[Z' ⊂ X']`: a Zariski frame `(U, f)` of `i`
pulls back to the Zariski frame `(e⁻¹ U, e^* f)` of `i'`, and the product of Kummer boundaries of
`f` restricts to that of `e^* f`. This is the argument of
`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_flat`, which needs no
flatness once the frames of `i'` are given.

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_thomFundamentalClass`.
- `AlgebraicGeometry.Etale.thomFundamentalClassMap_baseChange`: the same for the adjoint
  `cl_i : Λ_Z ⟶ Ri^!(Λ_X(c)[2c])`, through the base change map of `Ri^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {c : ℕ}
  {i : Z ⟶ X} [IsClosedImmersion i]

attribute [local instance] HasInvertibleExponent.opens

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: base change of the fundamental
class of a closed immersion with Thom frames, `[Z' ⊂ X'] = e^* [Z ⊂ X]`, along any morphism
`e : X' ⟶ X` such that the base change `i'` of `i` has Thom frames and regular Zariski frames. -/
theorem restrictSupportedClass_thomFundamentalClass (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k k' : Type u} [Field k] [Field k']
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] {X' Z' : Scheme.{u}}
    [HasInvertibleExponent Λ X'] (e : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i']
    (g : Z' ⟶ Z) (hg : IsPullback g i' i e) (hT' : HasThomFrames Λ c i')
    (hR' : HasRegularZariskiFrames c i') (aX' : X' ⟶ Spec (.of k')) [LocallyOfFiniteType aX'] :
    restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        (thomFundamentalClass Λ hT hR aX) = thomFundamentalClass Λ hT' hR' aX' := by
  refine hT'.eq_of_forall_exists_frameRestriction_eq fun z' ↦ ?_
  obtain ⟨F, hFo, ⟨w₀, hw₀⟩, -, -⟩ := hR (g z')
  have := hFo
  -- the preimage of the frame `F` in `X'`
  let W : X'.Opens := e ⁻¹ᵁ F.e.opensRange
  have hrange : Set.range (W.ι ≫ e).base ⊆ Set.range F.e.base := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  let a := IsOpenImmersion.lift F.e (W.ι ≫ e) hrange
  have hab : a ≫ F.e = W.ι ≫ e := IsOpenImmersion.lift_fac _ _ _
  let f' : Fin c → Γ(W.toScheme, ⊤) := fun t ↦ a.appTop (F.f t)
  obtain ⟨m, hm⟩ : ∃ m, IsPullback m (W.toScheme.zeroLocusSubschemeι (Set.range f'))
      (F.U.zeroLocusSubschemeι (Set.range F.f)) a :=
    ⟨_, isPullback_zeroLocusSubschemeι a (Set.range F.f) (Set.range f')
      (by rw [← Set.range_comp]; rfl)⟩
  have hout : IsPullback (m ≫ F.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range f')) i
      (W.ι ≫ e) := hab ▸ hm.paste_horiz F.isPullback
  let toZ := hg.lift (m ≫ F.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range f') ≫ W.ι)
    (by rw [hout.w, Category.assoc])
  have hH : IsPullback toZ (W.toScheme.zeroLocusSubschemeι (Set.range f')) i' W.ι :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout) (hg.lift_snd _ _ _) hg
  -- the pulled back frame of `i'`
  let H : i'.EtaleFrame c :=
    { U := W.toScheme
      e := W.ι
      etale := inferInstance
      f := f'
      toZ := toZ
      isPullback := hH }
  refine ⟨H, inferInstanceAs (IsOpenImmersion W.ι), ?_, ?_⟩
  · obtain ⟨p, hp⟩ : i' z' ∈ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      refine ⟨F.U.zeroLocusSubschemeι _ w₀, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← F.isPullback.w, Scheme.Hom.comp_apply, hw₀,
        ← Scheme.Hom.comp_apply, hg.w, Scheme.Hom.comp_apply]
    obtain ⟨q, hq, -⟩ := hH.exists_scheme_point z' p hp.symm
    exact ⟨q, hq⟩
  · rw [frameRestriction_thomFundamentalClass]
    have hF := frameRestriction_thomFundamentalClass Λ hT hR aX F
    rw [frameRestriction] at hF
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ W.ι e (W.ι ≫ e) rfl i i' _ g
      hg toZ hH (m ≫ F.toZ) hout, restrictSupportedClass_comp_tateShift Λ a F.e (W.ι ≫ e)
      hab.symm i _ _ F.toZ F.isPullback m hm (m ≫ F.toZ) hout, hF]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a F.f f' (fun _ ↦ rfl) m hm

/-- Base change of `cl_i : Λ_Z ⟶ Ri^!(Λ_X(c)[2c])`
(`AlgebraicGeometry.Etale.thomFundamentalClassMap`):
for the base change `i'` of `i` along any `e`, with Thom frames and regular Zariski frames,
`cl_{i'}` is `Λ_{Z'} ≅ Lg^* Λ_Z ⟶ Lg^* Ri^!(Λ_X(c)[2c]) ⟶ Ri'^! Le^*(Λ_X(c)[2c]) ≅
Ri'^!(Λ_{X'}(c)[2c])`. -/
theorem thomFundamentalClassMap_baseChange (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k k' : Type u} [Field k] [Field k']
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] {X' Z' : Scheme.{u}}
    [HasInvertibleExponent Λ X'] (e : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i']
    (g : Z' ⟶ Z) (hg : IsPullback g i' i e) (hT' : HasThomFrames Λ c i')
    (hR' : HasRegularZariskiFrames c i') (aX' : X' ⟶ Spec (.of k')) [LocallyOfFiniteType aX'] :
    thomFundamentalClassMap Λ hT' hR' aX' =
      (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (thomFundamentalClassMap Λ hT hR aX) ≫
          (rightDerivedUpperShriekBaseChangeMap Λ hg).app _ ≫
            (R(i')^![Λ]).map (leftDerivedUpperStarTateShiftIso Λ e c).hom := by
  rw [thomFundamentalClassMap, thomFundamentalClassMap,
    ← restrictSupportedClass_thomFundamentalClass Λ hT hR aX e i' g hg hT' hR' aX',
    supportedClassMap_restrictSupportedClass]

end Etale

end AlgebraicGeometry
