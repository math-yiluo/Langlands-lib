/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.ChartProbe

/-!
# Slopes on the affine blow-up charts

For `a, b ∈ I`, the chart `Spec A[I/a]` of the blow-up of `I` carries the *slope* `b/a`
(`AlgebraicGeometry.AffineBlowup.awaySlope`), the degree-one fraction `(b·X)/(a·X)` of the Rees
algebra. This file provides the algebraic kit for slopes, and shows that the charts at a
generating family of the centre cover the blow-up.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Slope

/-! ### Slopes on the affine blow-up charts

For `a, b ∈ I`, the chart `Spec A[I/a]` of the blow-up of `I` carries the *slope*
`b/a`, the degree-one fraction `(b·X)/(a·X)` of the Rees algebra. This section provides
the algebraic kit for slopes: linearity in the numerator, the identity
`(b/a)·a = b` over `A`, the transition formulas between two charts, and the fact that
the slopes of a generating family of `I` generate the unit ideal of the chart ring. -/

namespace AffineBlowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The slope `b/a` on the `a`-chart of the blow-up of `I`: the degree-one fraction
`(b·X)/(a·X)` of the Rees algebra of `I`. -/
def awaySlope {a : A} (ha : a ∈ I) {b : A} (hb : b ∈ I) :
    Away (reesGrading I) (reesX I a ha) :=
  HomogeneousLocalization.Away.mk (reesGrading I) (reesX_mem I a ha) 1 (reesX I b hb)
    (by simpa using reesX_mem I b hb)

variable {I}

/-- The slope `a/a` is `1`. -/
lemma awaySlope_self {a : A} (ha : a ∈ I) : awaySlope I ha ha = 1 := by
  rw [HomogeneousLocalization.ext_iff_val, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp [pow_one]⟩

/-- The slope of the zero numerator is `0`. -/
lemma awaySlope_zero {a : A} (ha : a ∈ I) (h0 : (0 : A) ∈ I) :
    awaySlope I ha h0 = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_zero]
  have h : reesX I 0 h0 = 0 := Subtype.ext (by simp)
  rw [h, Localization.mk_zero]

/-- Slopes are additive in the numerator. -/
lemma awaySlope_add {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hbc : b + c ∈ I) : awaySlope I ha hbc = awaySlope I ha hb + awaySlope I ha hc := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add, awaySlope,
    awaySlope, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.add_mk_self, reesX_add I hb hc]

/-- Slopes absorb ring multiples of the numerator through the structure map of the
chart ring. -/
lemma awaySlope_mul_left {a b : A} (r : A) (ha : a ∈ I) (hb : b ∈ I) (hrb : r * b ∈ I) :
    awaySlope I ha hrb = awayAlgebraMap I (reesX I a ha) r * awaySlope I ha hb := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, awaySlope,
    awaySlope, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    val_awayAlgebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial]

/-- Clearing the denominator of a slope: `(b/a) · a = b` in the chart ring. -/
lemma awaySlope_mul_awayAlgebraMap {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    awaySlope I ha hb * awayAlgebraMap I (reesX I a ha) a =
      awayAlgebraMap I (reesX I a ha) b := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, awaySlope,
    HomogeneousLocalization.Away.val_mk, val_awayAlgebraMap, val_awayAlgebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [mul_comm]

/-- **The slopes of a generating family generate the unit ideal of the chart ring.**
If `gen` generates `I` and `a ∈ I`, then `1 ∈ (gen k / a : k)` in `A[I/a]`: writing
`a = Σ cₖ · gen k` and dividing by `a` exhibits `1 = a/a` as a combination of the
slopes. -/
lemma one_mem_span_awaySlope {κ : Type*} (gen : κ → A) (hgen : ∀ k, gen k ∈ I)
    (hspan : Ideal.span (Set.range gen) = I) {a : A} (ha : a ∈ I) :
    (1 : Away (reesGrading I) (reesX I a ha)) ∈
      Ideal.span (Set.range fun k ↦ awaySlope I ha (hgen k)) := by
  rw [← awaySlope_self ha]
  have key : ∀ b (hb₀ : b ∈ Ideal.span (Set.range gen)), ∀ (hb : b ∈ I),
      awaySlope I ha hb ∈ Ideal.span (Set.range fun k ↦ awaySlope I ha (hgen k)) := by
    intro b hb₀
    induction hb₀ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact fun _ ↦ Ideal.subset_span ⟨k, rfl⟩
    | zero => exact fun h0 ↦ (awaySlope_zero ha h0) ▸ zero_mem _
    | add x y hx hy ihx ihy =>
        intro hxy
        have hxI : x ∈ I := hspan ▸ hx
        have hyI : y ∈ I := hspan ▸ hy
        rw [awaySlope_add ha hxI hyI hxy]
        exact add_mem (ihx hxI) (ihy hyI)
    | smul r x hx ihx =>
        intro hrx
        have hxI : x ∈ I := hspan ▸ hx
        rw [awaySlope_mul_left (b := x) r ha hxI hrx]
        exact Ideal.mul_mem_left _ _ (ihx hxI)
  exact key a (hspan.symm ▸ ha) ha

/-- The transition of a slope into the chart at a product: `(c/a)` maps to
`(c·b)/(a·b)` in `A[I/(a·b)]`-in-Rees-form. -/
lemma awayMap_awaySlope {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    {x : reesAlgebra I} (hx : x = reesX I a ha * reesX I b hb) :
    awayMap (reesGrading I) (reesX_mem I b hb) hx (awaySlope I ha hc) =
      HomogeneousLocalization.Away.mk (reesGrading I)
        (hx ▸ SetLike.mul_mem_graded (reesX_mem I a ha) (reesX_mem I b hb)) 1
        (reesX I c hc * reesX I b hb)
        (by simpa using SetLike.mul_mem_graded (reesX_mem I c hc) (reesX_mem I b hb)) := by
  rw [awaySlope, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [pow_one]

/-- **Chart transitions of slopes**: if `c · b = c' · a` in `A`, then the slope `c/a`
of the `a`-chart and the slope `c'/b` of the `b`-chart agree on the overlap
`A[I/(a·b)]`. This exact-identity form is what the elimination-of-indeterminacy
construction arranges by clearing denominators. -/
lemma awayMap_awaySlope_eq {a b c c' : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hc' : c' ∈ I) (h : c * b = c' * a) :
    awayMap (reesGrading I) (reesX_mem I b hb) rfl (awaySlope I ha hc) =
      awayMap (reesGrading I) (reesX_mem I a ha)
        (mul_comm (reesX I a ha) (reesX I b hb)) (awaySlope I hb hc') := by
  rw [awayMap_awaySlope ha hb hc rfl,
    awayMap_awaySlope hb ha hc' (mul_comm (reesX I a ha) (reesX I b hb)),
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial, h]

/-- The transition maps of the blow-up charts intertwine the structure maps from `A`. -/
lemma awayMap_awayAlgebraMap_apply {a : A} (ha : a ∈ I) {g : reesAlgebra I}
    (hg : g ∈ reesGrading I 1) {x : reesAlgebra I} (hx : x = reesX I a ha * g) (r : A) :
    awayMap (reesGrading I) hg hx (awayAlgebraMap I (reesX I a ha) r) =
      awayAlgebraMap I x r :=
  awayMap_fromZeroRingHom (reesGrading I) hg hx ((reesGradingZero I) r)


/-- The `Away.isLocalizationElem` of two degree-one Rees elements is the slope. -/
lemma isLocalizationElem_eq_awaySlope {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I a ha) (reesX_mem I b hb) =
      awaySlope I ha hb := by
  rw [HomogeneousLocalization.ext_iff_val, awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, pow_one]

/-- **Passing between blow-up charts**: if the image of `b` is invertible at a point of the
`a`-chart, that point lies in the `b`-chart. -/
lemma mem_range_chart_of_mem_basicOpen {a b : A} (ha : a ∈ I) (hb : b ∈ I)
    (y : Spec (.of (HomogeneousLocalization.Away (reesGrading I) (reesX I a ha))))
    (hy : y ∈ PrimeSpectrum.basicOpen (awayAlgebraMap I (reesX I a ha) b)) :
    chart I (reesX I a ha) (reesX_mem I a ha) y ∈
      Set.range (chart I (reesX I b hb) (reesX_mem I b hb)) := by
  have hmem : y ∈ chart I (reesX I a ha) (reesX_mem I a ha) ⁻¹ᵁ
      Proj.basicOpen (reesGrading I) (reesX I b hb) := by
    rw [chart, Proj.awayι_preimage_basicOpen (𝒜 := reesGrading I)
      (reesX_mem I a ha) one_pos (reesX_mem I b hb) one_pos,
      isLocalizationElem_eq_awaySlope ha hb]
    have hfac : awayAlgebraMap I (reesX I a ha) b =
        awaySlope I ha hb * awayAlgebraMap I (reesX I a ha) a :=
      (awaySlope_mul_awayAlgebraMap ha hb).symm
    rw [hfac, PrimeSpectrum.basicOpen_mul] at hy
    exact hy.1
  rw [← opensRange_chart I (reesX I b hb) (reesX_mem I b hb)] at hmem
  exact hmem

end AffineBlowup

end Slope

section ChartCover

/-! ### The charts at a generating family cover the blow-up -/

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- If `gen` generates `I`, every degree-one element `b·X` of the Rees algebra lies in
the ideal generated by the `gen k · X`. -/
lemma reesX_mem_span_reesX {κ : Type*} (gen : κ → A) (hgen : ∀ k, gen k ∈ I)
    (hspan : Ideal.span (Set.range gen) = I) {b : A} (hb : b ∈ I) :
    reesX I b hb ∈ Ideal.span (Set.range fun k ↦ reesX I (gen k) (hgen k)) := by
  have key : ∀ x (hx₀ : x ∈ Ideal.span (Set.range gen)), ∀ (hx : x ∈ I),
      reesX I x hx ∈ Ideal.span (Set.range fun k ↦ reesX I (gen k) (hgen k)) := by
    intro x hx₀
    induction hx₀ using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact fun _ ↦ Ideal.subset_span ⟨k, rfl⟩
    | zero =>
        intro h0
        have h : reesX I 0 h0 = 0 := Subtype.ext (by simp)
        exact h ▸ zero_mem _
    | add x y hx hy ihx ihy =>
        intro hxy
        have hxI : x ∈ I := hspan ▸ hx
        have hyI : y ∈ I := hspan ▸ hy
        rw [reesX_add I hxI hyI]
        exact add_mem (ihx hxI) (ihy hyI)
    | smul r x hx ihx =>
        intro hrx
        have hxI : x ∈ I := hspan ▸ hx
        have h : reesX I (r • x) hrx = algebraMap A (reesAlgebra I) r * reesX I x hxI :=
          Subtype.ext (by simp [Polynomial.C_mul_monomial])
        rw [h]
        exact Ideal.mul_mem_left _ _ (ihx hxI)
  exact key b (hspan.symm ▸ hb) hb

/-- **The charts at a generating family cover the blow-up**: if `gen` generates `I`,
the basic opens of `Proj` of the Rees algebra at the degree-one elements `gen k · X`
cover it. -/
lemma iSup_basicOpen_reesX_gen_eq_top {κ : Type*} (gen : κ → A) (hgen : ∀ k, gen k ∈ I)
    (hspan : Ideal.span (Set.range gen) = I) :
    ⨆ k, Proj.basicOpen (reesGrading I) (reesX I (gen k) (hgen k)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (reesGrading I) _
    ((irrelevant_le_span_range_reesX I).trans (Ideal.span_le.mpr (by
      rintro - ⟨b, rfl⟩
      exact reesX_mem_span_reesX I gen hgen hspan b.2)))

/-- **The charts at a generating family cover the blow-up over an affine open.** -/
lemma Scheme.IdealSheafData.exists_mem_range_blowupChart_of_span (I : X.IdealSheafData)
    (V : X.affineOpens) {κ : Type*} {gen : κ → Γ(X, V.1)} (hgen : ∀ k, gen k ∈ I.ideal V)
    (hspan : Ideal.span (Set.range gen) = I.ideal V) {x : I.blowup}
    (hx : x ∈ I.blowupMap ⁻¹ᵁ V.1) :
    ∃ (k : κ) (y : _), x = I.blowupChart V (hgen k) y := by
  rw [I.blowupMap_preimage V] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ (⊤ : (AffineBlowup (I.ideal V)).Opens) := trivial
  rw [← iSup_basicOpen_reesX_gen_eq_top (I.ideal V) gen hgen hspan] at hy
  obtain ⟨k, hyk⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← AffineBlowup.opensRange_chart (I.ideal V) (reesX (I.ideal V) (gen k) (hgen k))
    (reesX_mem (I.ideal V) (gen k) (hgen k))] at hyk
  obtain ⟨z, hz⟩ := hyk
  exact ⟨k, z, by rw [Scheme.IdealSheafData.blowupChart, Scheme.Hom.comp_apply, hz]⟩

end ChartCover

end AlgebraicGeometry
