/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening

/-!
# Open pieces of universal first order thickenings

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
the general remarks preceding the affine case
(blueprint: lem-weil-pbc-universal-thickening-open-pieces).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem firstOrder_surjective {T T' : Scheme.{u}} (i : T ⟶ T')
    (hi : IsFirstOrderThickening i) : Function.Surjective i := by
  have : IsClosedImmersion i := hi.1
  have hs : i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ i.ker 1, hi.2]
    exact Scheme.IdealSheafData.support_bot
  apply Set.range_eq_univ.mp
  rw [← i.isClosedEmbedding.isClosed_range.closure_eq, ← i.support_ker, hs]
  rfl

private theorem firstOrder_restrict {T T' : Scheme.{u}} (i : T ⟶ T')
    (hi : IsFirstOrderThickening i) (W' : T'.Opens) :
    IsFirstOrderThickening (i ∣_ W') := by
  have : IsClosedImmersion i := hi.1
  refine ⟨inferInstance, Scheme.IdealSheafData.ext ?_⟩
  funext Q
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.ker_morphismRestrict_ideal]
  have hQ := congrArg (fun I => I.ideal
    ⟨W'.ι ''ᵁ Q, Q.2.image_of_isOpenImmersion W'.ι⟩) hi.2
  simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using hQ

/-- Restriction of a first order thickening, restriction of a universal thickening to
opens of source and base, and enlargement of an open base containing the image.
In the first clause, for any structure morphism `b : T' ⟶ X`, the restricted structure
morphism is `W'.ι ≫ b`; the source is over `X` by composition. The equality on affine
opens expresses restriction of the defining ideal sheaf, in Mathlib's ideal-sheaf data.

Source: Stacks Project, proof of Lemma 37.7.1 (Tag 04F3), general remarks
(blueprint: lem-weil-pbc-universal-thickening-open-pieces).

Proof:
1. Apply lem-weil-pbc-thickening-open-restriction to `iT` and `W'`, with the whole
   base as its open. The restricted immersion is closed, its ideal is the restricted
   ideal, and this ideal still has square zero. This proves the first clause over any
   base, using def-sbc-first-order-thickening.
2. A first order thickening is a homeomorphism on underlying spaces. The image of
   each open `W` is open and is its unique inverse under preimage. This also supplies
   the unique open `V'` corresponding to `V` in the second clause.
3. Every point of `V'` is `i(v)` with `v` in `V`. Since `i ≫ h' = h`, its image
   under `h'` lies in `U`. Factor the restricted maps through the opens by
   lem-weil-pbc-morphism-factors-through-open-subscheme; restriction of the thickening
   gives a first order thickening of `V` over `U`, compatible with the restricted `h`.
4. Given a test thickening over `U` and a map to `V`, compose with the inclusions to
   obtain a test over `X`. Apply def-weil-pbc-universal-first-order-thickening to get
   the unique extension into `Z'`. Surjectivity on points of the test thickening
   places its image in `V'`, so it factors uniquely through `V'`. Cancel the open
   inclusions to verify its two required compatibilities over `U`.
5. Two such extensions into `V'` become extensions into `Z'`; universal uniqueness
   makes them equal after inclusion, and cancellation of that inclusion proves
   uniqueness into `V'`. This proves universality of the restricted thickening.
6. For enlargement of the base, the immersion and its square-zero ideal are unchanged;
   composing the structure morphism with `U.ι` makes a thickening over `X` for `h`.
7. In any test over `X` mapping to `Z`, surjectivity on points of its immersion and
   the containment of `h(Z)` in `U` force the structure map of the test to factor
   through `U`. Cancel `U.ι` to verify the compatibility, then apply universality
   over `U` to obtain the required extension over `X`.
8. Any other extension over `X` is over `U` after cancelling `U.ι`, and uniqueness
   over `U` identifies the two. This proves the third clause. -/
theorem universalFirstOrderThickening_open_pieces {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (∀ {T T' : Scheme.{u}} (iT : T ⟶ T') (_b : T' ⟶ X),
      IsFirstOrderThickening iT →
      (∀ W' : T'.Opens,
        IsFirstOrderThickening (iT ∣_ W') ∧
          ∀ Q : W'.toScheme.affineOpens,
            (iT ∣_ W').ker.ideal Q =
              iT.ker.ideal ⟨W'.ι ''ᵁ Q, Q.2.image_of_isOpenImmersion W'.ι⟩) ∧
      (∀ W : T.Opens, ∃! W' : T'.Opens, iT ⁻¹ᵁ W' = W)) ∧
    (∀ {Z' : Scheme.{u}} (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h' →
      ∀ (V : Z.Opens) (U : X.Opens), V ≤ h ⁻¹ᵁ U →
        ∃ V' : Z'.Opens, i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          ∃ (iV : V.toScheme ⟶ V'.toScheme) (hV : V.toScheme ⟶ U.toScheme)
            (hV' : V'.toScheme ⟶ U.toScheme),
            iV ≫ V'.ι = V.ι ≫ i ∧ hV ≫ U.ι = V.ι ≫ h ∧
              hV' ≫ U.ι = V'.ι ≫ h' ∧ IsUniversalFirstOrderThickening hV iV hV') ∧
    (∀ (U : X.Opens) (hU : Z ⟶ U.toScheme), hU ≫ U.ι = h →
      ∀ {Z' : Scheme.{u}} (i : Z ⟶ Z') (hU' : Z' ⟶ U.toScheme),
        IsUniversalFirstOrderThickening hU i hU' →
          IsUniversalFirstOrderThickening h i (hU' ≫ U.ι)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T T' iT b hiT
    have : IsClosedImmersion iT := hiT.1
    refine ⟨?_, ?_⟩
    · intro W'
      exact ⟨firstOrder_restrict iT hiT W', Scheme.ker_morphismRestrict_ideal iT W'⟩
    · intro W
      let e := (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨iT.isClosedEmbedding.isEmbedding, firstOrder_surjective iT hiT⟩).homeomorph
      refine ⟨e.opensCongr W, ?_, ?_⟩
      · exact e.opensCongr.symm_apply_apply W
      · intro W' hW'
        exact e.opensCongr.symm.injective (hW'.trans (e.opensCongr.symm_apply_apply W).symm)
  · intro Z' i h' H V U hVU
    have : IsClosedImmersion i := H.1.1
    let e := (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, firstOrder_surjective i H.1⟩).homeomorph
    obtain ⟨V', hV'⟩ : ∃ V' : Z'.Opens, i ⁻¹ᵁ V' = V :=
      ⟨e.opensCongr V, e.opensCongr.symm_apply_apply V⟩
    subst V
    have hV'U : V' ≤ h' ⁻¹ᵁ U := by
      intro z' hz'
      obtain ⟨z, rfl⟩ := firstOrder_surjective i H.1 z'
      have hz := hVU hz'
      change h' (i z) ∈ U
      rw [← Scheme.Hom.comp_apply, H.2.1]
      exact hz
    let iV := i ∣_ V'
    let hV := h.resLE U (i ⁻¹ᵁ V') hVU
    let hV' := h'.resLE U V' hV'U
    have hiVι : iV ≫ V'.ι = (i ⁻¹ᵁ V').ι ≫ i :=
      morphismRestrict_ι i V'
    have hhV : hV ≫ U.ι = (i ⁻¹ᵁ V').ι ≫ h := h.resLE_comp_ι hVU
    have hhV' : hV' ≫ U.ι = V'.ι ≫ h' := h'.resLE_comp_ι hV'U
    refine ⟨V', rfl, hV'U, iV, hV, hV', hiVι, hhV, hhV',
      firstOrder_restrict i H.1 V', ?_, ?_⟩
    · apply (cancel_mono U.ι).mp
      rw [Category.assoc, hhV', ← Category.assoc, hiVι,
        Category.assoc, H.2.1, hhV]
    · intro T T' j b a hj hab
      have habX : j ≫ (b ≫ U.ι) = (a ≫ (i ⁻¹ᵁ V').ι) ≫ h := by
        rw [← Category.assoc, hab, Category.assoc, hhV, ← Category.assoc]
      obtain ⟨a'', ha'', huniq⟩ := H.2.2 j (b ≫ U.ι) (a ≫ (i ⁻¹ᵁ V').ι) hj habX
      have haV' : Set.range a'' ⊆ Set.range V'.ι := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨t', rfl⟩
        obtain ⟨t, rfl⟩ := firstOrder_surjective j hj t'
        have ht := congrArg (fun f : T ⟶ Z' => f t) ha''.2
        simp only [Scheme.Hom.comp_apply] at ht
        rw [ht]
        exact (a t).2
      let a' := IsOpenImmersion.lift V'.ι a'' haV'
      have ha'ι : a' ≫ V'.ι = a'' := IsOpenImmersion.lift_fac V'.ι a'' haV'
      have ha' : a' ≫ hV' = b ∧ j ≫ a' = a ≫ iV := by
        constructor
        · apply (cancel_mono U.ι).mp
          rw [Category.assoc, hhV', ← Category.assoc, ha'ι, ha''.1]
        · apply (cancel_mono V'.ι).mp
          rw [Category.assoc, ha'ι, ha''.2]
          simp only [Category.assoc, hiVι]
      refine ⟨a', ha', ?_⟩
      intro a₁ ha₁
      apply (cancel_mono V'.ι).mp
      have ha₁X : (a₁ ≫ V'.ι) ≫ h' = b ≫ U.ι ∧
          j ≫ (a₁ ≫ V'.ι) = (a ≫ (i ⁻¹ᵁ V').ι) ≫ i := by
        constructor
        · rw [Category.assoc, ← hhV', ← Category.assoc, ha₁.1]
        · rw [← Category.assoc, ha₁.2, Category.assoc, hiVι, ← Category.assoc]
      exact (huniq _ ha₁X).trans ha'ι.symm
  · intro U hU hhU Z' i hU' H
    refine ⟨H.1, ?_, ?_⟩
    · rw [← Category.assoc, H.2.1, hhU]
    · intro T T' j b a hj hab
      have hb : Set.range b ⊆ Set.range U.ι := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨t', rfl⟩
        obtain ⟨t, rfl⟩ := firstOrder_surjective j hj t'
        have ht := congrArg (fun f : T ⟶ X => f t) hab
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at ht
        rw [ht, ← hhU, Scheme.Hom.comp_apply]
        exact (hU (a t)).2
      let bU := IsOpenImmersion.lift U.ι b hb
      have hbU : bU ≫ U.ι = b := IsOpenImmersion.lift_fac U.ι b hb
      have habU : j ≫ bU = a ≫ hU := by
        apply (cancel_mono U.ι).mp
        rw [Category.assoc, hbU, Category.assoc, hhU, hab]
      obtain ⟨a', ha', huniq⟩ := H.2.2 j bU a hj habU
      refine ⟨a', ⟨?_, ha'.2⟩, ?_⟩
      · rw [← Category.assoc, ha'.1, hbU]
      · intro a'' ha''
        apply huniq a''
        refine ⟨?_, ha''.2⟩
        apply (cancel_mono U.ι).mp
        rw [Category.assoc, ha''.1, hbU]

end AlgebraicGeometry
