/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.DiagonalSectionRestriction

/-!
# Fundamental classes of rational points as restrictions of the diagonal

Let `a : X ⟶ S` be a morphism with a section `y`. The point `y : S ⟶ X` is the base change of
the diagonal `Δ : X ⟶ X ×_S X` along the section `j_y = (𝟙, a ≫ y)` of the first projection
(`AlgebraicGeometry.Etale.isPullback_diagonal_pullbackLiftSection`). For `S = Spec k` and `X`
smooth over the perfect field `k`, the fundamental class `[y ⊂ X]` is therefore the restriction
of the fundamental class `[Δ ⊂ X ×_k X]` along `j_y`: Zariski frames of a regular immersion
restrict to frames of its base change as soon as the base change is again a regular immersion
of the same codimension, which is the case here although `j_y` is not flat
(`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_isPullback`).

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_isPullback`: base change
  of the fundamental class to a base change which is regular of the same codimension.
- `AlgebraicGeometry.Etale.isPullback_diagonal_pullbackLiftSection`: the section `y` is the
  base change of the diagonal along `j_y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- A section `y` of `a : X ⟶ S` is the base change of the diagonal `Δ : X ⟶ X ×_S X` along the
section `j_y = (𝟙, a ≫ y)` of the first projection: `(z, y(a(z))) = (w, w)` forces
`z = w = y(a(z))`. -/
lemma isPullback_diagonal_pullbackLiftSection {X S : Scheme.{u}} (a : X ⟶ S) (y : S ⟶ X)
    (hy : y ≫ a = 𝟙 S) :
    IsPullback y y (pullback.diagonal a) (pullbackLiftSection a y hy) := by
  have w : y ≫ pullback.diagonal a = y ≫ pullbackLiftSection a y hy := by
    ext <;> simp [reassoc_of% hy]
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w (fun s ↦ s.snd ≫ a) ?_ ?_ ?_)
  all_goals
    intro s
    have h₁ := congrArg (· ≫ pullback.fst a a) s.condition
    have h₂ := congrArg (· ≫ pullback.snd a a) s.condition
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      pullbackLiftSection_fst, pullbackLiftSection_snd, Category.comp_id] at h₁ h₂
  · rw [Category.assoc, h₂]
  · rw [Category.assoc, ← h₂, h₁]
  · intro m _ hm
    rw [← hm, Category.assoc, hy, Category.comp_id]

attribute [local instance] HasInvertibleExponent.opens

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

**Base change of the fundamental class to a regular immersion of the same codimension**,
`[Z' ⊂ X'] = e^* [Z ⊂ X]`: for any `e : X' ⟶ X` with `X'` smooth over `k` whose base change
`i' : Z' ⟶ X'` of `i` is a regular immersion of the same codimension `c`, with `Z'` regular,
the restriction of supports along `e` carries the fundamental class of `i` to that of `i'`.
Near a point of `Z'`, a Zariski frame `(U, f)` of `i` pulls back to the Zariski frame
`(e⁻¹ U, e^* f)` of `i'`, and the product of Kummer boundaries of `f` restricts to that of
`e^* f`. This generalizes
`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_flat`, where flatness of `e`
serves only to make `i'` regular. -/
theorem restrictSupportedClass_fundamentalClass_of_isPullback (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) {X' Z' : Scheme.{u}}
    (e : X' ⟶ X) [Smooth (e ≫ aX)] (i' : Z' ⟶ X') [IsRegularImmersion c i'] (g : Z' ⟶ Z)
    (hg : IsPullback g i' i e) (hZ' : ∀ z : Z', IsRegularLocalRing (Z'.presheaf.stalk z)) :
    haveI : HasInvertibleExponent Λ X' := .of_hom e
    restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        (fundamentalClass Λ c i aX hZ) = fundamentalClass Λ c i' (e ≫ aX) hZ' := by
  have : HasInvertibleExponent Λ X' := .of_hom e
  refine eq_of_forall_exists_frameRestriction_eq Λ c i' (e ≫ aX) hZ' fun z' ↦ ?_
  obtain ⟨F, hFo, ⟨w₀, hw₀⟩, -, -⟩ := i.exists_etaleFrame_isOpenImmersion c (g z')
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
  · rw [frameRestriction_fundamentalClass]
    have hF := frameRestriction_fundamentalClass Λ c i aX hZ F
    rw [frameRestriction] at hF
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ W.ι e (W.ι ≫ e) rfl i i' _ g
      hg toZ hH (m ≫ F.toZ) hout, restrictSupportedClass_comp_tateShift Λ a F.e (W.ι ≫ e)
      hab.symm i _ _ F.toZ F.isPullback m hm (m ≫ F.toZ) hout, hF]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a F.f f' (fun _ ↦ rfl) m hm

end Etale

end AlgebraicGeometry
