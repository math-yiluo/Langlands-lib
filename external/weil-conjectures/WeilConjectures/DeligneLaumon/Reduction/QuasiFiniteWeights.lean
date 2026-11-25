/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk

/-!
# Weights of quasi-finite direct images

Let `f : X ⟶ Y` be a separated quasi-finite morphism of `k₀`-schemes and `F` a Weil sheaf on `X`.
At a closed point `y` of `Y` of degree `d`, the Frobenius `F_y` on `(f₀!F)_ȳ` satisfies

`det (1 - T F_y ∣ (f₀!F)_ȳ) = ∏_{x ↦ y} det (1 - T^{e_x} F_x ∣ F_x̄)`, `e_x = [κ(x) : κ(y)]`

(`WeilSheaf.exists_charpolyRev_stalk_higherLowerShriek_zero`). Hence every eigenvalue `β` of
`F_y` has a power `β^{e_x}` which is an eigenvalue of some `F_x`, and since `q_x = q_y ^ {e_x}`,
the normalized weights of `β` and of `β^{e_x}` agree. So `f₀!` preserves upper weight bounds,
punctual purity and `ι`-reality. The same holds for `H_c^0` of a scheme quasi-finite over `k₀`,
and conversely for a scheme with a single point.

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite`: blueprint
  `lemma-finite-quasi-finite-direct-images`, part 3.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.higherLowerShriek_zero_of_quasiFinite`,
  `AlgebraicGeometry.WeilSheaf.IsReal.higherLowerShriek_zero_of_quasiFinite`.
- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.compactlySupportedCohomology_zero`,
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.compactlySupportedCohomology_zero`,
  `AlgebraicGeometry.WeilSheaf.IsReal.compactlySupportedCohomology_zero`, and the converses
  `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_of_compactlySupportedCohomology_zero`,
  `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_of_compactlySupportedCohomology_zero`,
  `AlgebraicGeometry.WeilSheaf.isReal_of_compactlySupportedCohomology_zero` for a single point.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Numerics

/-- Comparison of normalized weights: for `e ≠ 0`, `a ^ e ≤ (Q ^ e) ^ w ↔ a ≤ Q ^ w`. -/
private theorem pow_le_natCast_pow_rpow_iff {a : ℝ} (ha : 0 ≤ a) (Q : ℕ) {e : ℕ} (he : e ≠ 0)
    (w : ℝ) : a ^ e ≤ ((Q ^ e : ℕ) : ℝ) ^ w ↔ a ≤ (Q : ℝ) ^ w := by
  rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
  exact pow_le_pow_iff_left₀ ha (Real.rpow_nonneg (Nat.cast_nonneg _) _) he

/-- Comparison of normalized weights: for `e ≠ 0`, `a ^ e = (Q ^ e) ^ w ↔ a = Q ^ w`. -/
private theorem pow_eq_natCast_pow_rpow_iff {a : ℝ} (ha : 0 ≤ a) (Q : ℕ) {e : ℕ} (he : e ≠ 0)
    (w : ℝ) : a ^ e = ((Q ^ e : ℕ) : ℝ) ^ w ↔ a = (Q : ℝ) ^ w := by
  rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
  exact pow_left_inj₀ ha (Real.rpow_nonneg (Nat.cast_nonneg _) _) he

end Numerics

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

section DirectImage

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The eigenvalues of the local Frobenius of a quasi-finite direct image: every eigenvalue `β`
of `F_y` on `(f₀!F)_ȳ` has a power `β ^ e` which is an eigenvalue of `F_x` on `F_x̄` for a closed
point `x` above `y` with `deg x = e · deg y`. -/
theorem WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_stalk_higherLowerShriek_zero
    (F : WeilSheaf k₀ l X) {y : Y.finitePoints} {β : PadicAlgCl l}
    (hβ : (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobeniusEnd.HasEigenvalue β) :
    ∃ (x : X.finitePoints) (e : ℕ), f.base x.1 = y.1 ∧ e ≠ 0 ∧
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 =
        (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 * e ∧
      (F.stalk x).frobeniusEnd.HasEigenvalue (β ^ e) := by
  obtain ⟨s, hs, hA⟩ := F.exists_charpolyRev_stalk_higherLowerShriek_zero f y
  obtain ⟨x, hx, hxβ⟩ := LinearMap.exists_hasEigenvalue_pow_of_charpolyRev_eq _ s
    (fun x ↦ (F.stalk x).frobeniusEnd) _ hA hβ (FrobeniusModule.ne_zero_of_hasEigenvalue hβ)
  have hfx := (hs x).1 hx
  have hdvd := Scheme.Hom.degreeOver_dvd_of_isOver (k₀ := k₀) f x.2
  rw [hfx] at hdvd
  have hde := Nat.mul_div_cancel' hdvd
  refine ⟨x, _, hfx, fun h0 ↦ ?_, hde.symm, hxβ⟩
  rw [h0, mul_zero] at hde
  exact Scheme.Hom.degreeOver_ne_zero _ x.2 hde.symm

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves punctual upper weight bounds (blueprint: `lemma-finite-quasi-finite-direct-images`,
`lemma-finite-quasi-finite-direct-images`, part 3): at a closed point `y` the Frobenius permutes the
points above `y`; on an orbit of length `e` an eigenvalue `α` upstairs contributes eigenvalues `β`
with `βᵉ = α` downstairs, whose normalized weights agree because `q_x = q_yᵉ`. -/
theorem WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).HasWeightsAtMost ι w := by
  intro y β hβ
  obtain ⟨x, e, -, he, hdeg, hx⟩ :=
    F.exists_hasEigenvalue_stalk_of_hasEigenvalue_stalk_higherLowerShriek_zero f hβ
  have hw := h x _ hx
  simp only [Scheme.Hom.residueCard, hdeg, pow_mul, map_pow, norm_pow] at hw
  exact (pow_le_natCast_pow_rpow_iff (norm_nonneg _) _ he _).1 hw

/-- For a separated quasi-finite morphism `f` of `k₀`-schemes the exact functor `f₀!` preserves
punctual purity of weight `w` (blueprint: `lemma-finite-quasi-finite-direct-images`): every
eigenvalue `β` of the local Frobenius at `y` has a power `βᵉ` which is an eigenvalue at a point `x`
above `y` with `q_x = q_yᵉ`. -/
theorem WeilSheaf.IsPunctuallyPureOfWeight.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.IsPunctuallyPureOfWeight ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).IsPunctuallyPureOfWeight ι w := by
  intro y β hβ
  obtain ⟨x, e, -, he, hdeg, hx⟩ :=
    F.exists_hasEigenvalue_stalk_of_hasEigenvalue_stalk_higherLowerShriek_zero f hβ
  have hw := h x _ hx
  simp only [Scheme.Hom.residueCard, hdeg, pow_mul, map_pow, norm_pow] at hw
  exact (pow_eq_natCast_pow_rpow_iff (norm_nonneg _) _ he _).1 hw

/-- For a separated quasi-finite morphism `f` of `k₀`-schemes the exact functor `f₀!` preserves
`ι`-reality: the local polynomial of `f₀!F` at `y` is a product of expansions
`det (1 - T^{e_x} F_x)` of local polynomials of `F`. -/
theorem WeilSheaf.IsReal.higherLowerShriek_zero_of_quasiFinite {F : WeilSheaf k₀ l X}
    (h : F.IsReal ι) : ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).IsReal ι := by
  have isReal_of_charpolyRev_eq_prod {α : Type u}
      (M : FrobeniusModule.{u + 1, 0} (PadicAlgCl l))
      (N : α → FrobeniusModule.{u + 1, 0} (PadicAlgCl l)) (s : Finset α) (e : α → ℕ)
      (hM : M.frobeniusEnd.charpolyRev =
        ∏ x ∈ s, Polynomial.expand _ (e x) (N x).frobeniusEnd.charpolyRev)
      (he : ∀ x ∈ s, e x ≠ 0) (hN : ∀ x ∈ s, (N x).IsReal ι) : M.IsReal ι := by
    intro n
    rw [FrobeniusModule.localPolynomial, hM]
    exact Polynomial.coeff_prod_fixed ι (starRingEnd ℂ) s _ (fun x hx ↦
      (Polynomial.forall_coeff_expand_fixed_iff ι _ (he x hx) _).2 (hN x hx)) n
  intro y
  obtain ⟨s, hs, hA⟩ := F.exists_charpolyRev_stalk_higherLowerShriek_zero f y
  refine isReal_of_charpolyRev_eq_prod _ (fun x : X.finitePoints ↦ F.stalk x) s
    (fun x ↦ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 /
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1) hA ?_ (fun x _ ↦ h x)
  intro x hx
  have hdvd := Scheme.Hom.degreeOver_dvd_of_isOver (k₀ := k₀) f x.2
  rw [(hs x).1 hx] at hdvd
  exact (Nat.div_ne_zero_iff_of_dvd hdvd).2
    ⟨Scheme.Hom.degreeOver_ne_zero _ x.2, Scheme.Hom.degreeOver_ne_zero _ y.2⟩

end DirectImage

section CompactlySupportedCohomology

variable {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (T ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [LocallyQuasiFinite (T ↘ Spec (CommRingCat.of k₀))]
  {G : WeilSheaf k₀ l T}

/-- Every eigenvalue `β` of the Frobenius on `H_c^0` of a scheme quasi-finite over `k₀` has a
power `β ^ {deg t}` which is an eigenvalue of the local Frobenius at a closed point `t`. -/
theorem WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_compactlySupportedCohomology_zero
    {β : PadicAlgCl l} (hβ : (G.compactlySupportedCohomology 0).frobeniusEnd.HasEigenvalue β) :
    ∃ t : T.finitePoints,
      (G.stalk t).frobeniusEnd.HasEigenvalue
        (β ^ (T ↘ Spec (CommRingCat.of k₀)).degreeOver t.1) := by
  have : Finite T :=
    Scheme.Hom.finite_of_locallyQuasiFinite_toSpecField (T ↘ Spec (CommRingCat.of k₀))
  let : Fintype T.finitePoints := Fintype.ofFinite _
  obtain ⟨t, -, ht⟩ := LinearMap.exists_hasEigenvalue_pow_of_charpolyRev_eq _ Finset.univ
    (fun t ↦ (G.stalk t).frobeniusEnd) _
    G.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite hβ
    (FrobeniusModule.ne_zero_of_hasEigenvalue hβ)
  exact ⟨t, ht⟩

/-- On a scheme quasi-finite over `k₀`, punctual weights at most `w` give weights at most `w` on
`H_c^0`, relative to `q = #k₀`. -/
theorem WeilSheaf.HasWeightsAtMost.compactlySupportedCohomology_zero {w : ℝ}
    (h : G.HasWeightsAtMost ι w) :
    (G.compactlySupportedCohomology 0).HasWeightsAtMostOver k₀ ι w := by
  intro β hβ
  obtain ⟨t, ht⟩ :=
    WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_compactlySupportedCohomology_zero hβ
  have hw := h t _ ht
  simp only [Scheme.Hom.residueCard, map_pow, norm_pow] at hw
  exact (pow_le_natCast_pow_rpow_iff (norm_nonneg _) _
    (Scheme.Hom.degreeOver_ne_zero _ t.2) _).1 hw

/-- On a scheme quasi-finite over `k₀`, punctual purity of weight `w` gives purity of weight `w`
of `H_c^0`, relative to `q = #k₀`. -/
theorem WeilSheaf.IsPunctuallyPureOfWeight.compactlySupportedCohomology_zero {w : ℝ}
    (h : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 0).IsPureOfWeightOver k₀ ι w := by
  intro β hβ
  obtain ⟨t, ht⟩ :=
    WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_compactlySupportedCohomology_zero hβ
  have hw := h t _ ht
  simp only [Scheme.Hom.residueCard, map_pow, norm_pow] at hw
  exact (pow_eq_natCast_pow_rpow_iff (norm_nonneg _) _
    (Scheme.Hom.degreeOver_ne_zero _ t.2) _).1 hw

/-- On a scheme quasi-finite over `k₀`, `H_c^0` of an `ι`-real Weil sheaf is `ι`-real: its local
polynomial is the product of the expansions `det (1 - T^{deg t} F_t)`. -/
theorem WeilSheaf.IsReal.compactlySupportedCohomology_zero (h : G.IsReal ι) :
    (G.compactlySupportedCohomology 0).IsReal ι := by
  have : Finite T :=
    Scheme.Hom.finite_of_locallyQuasiFinite_toSpecField (T ↘ Spec (CommRingCat.of k₀))
  let : Fintype T.finitePoints := Fintype.ofFinite _
  intro n
  rw [FrobeniusModule.localPolynomial,
    G.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite]
  exact Polynomial.coeff_prod_fixed ι (starRingEnd ℂ) _ _ (fun t _ ↦
    (Polynomial.forall_coeff_expand_fixed_iff ι _ (Scheme.Hom.degreeOver_ne_zero _ t.2) _).2
      (h t)) n

variable [Subsingleton T]

/-- On a scheme with a single point, quasi-finite over `k₀`, weights at most `v` on `H_c^0`
(relative to `q = #k₀`) give punctual weights at most `v`: the local polynomial of `H_c^0` is
`det (1 - T^d F_t)`, so every eigenvalue of `F_t` is the `d`-th power of one on `H_c^0`. -/
theorem WeilSheaf.hasWeightsAtMost_of_compactlySupportedCohomology_zero {v : ℝ}
    (h : (G.compactlySupportedCohomology 0).HasWeightsAtMostOver k₀ ι v) :
    G.HasWeightsAtMost ι v := by
  intro t γ hγ
  have hd := Scheme.Hom.degreeOver_ne_zero (T ↘ Spec (CommRingCat.of k₀)) t.2
  obtain ⟨β, hβ, rfl⟩ := LinearMap.exists_hasEigenvalue_pow_eq_of_charpolyRev_eq_expand _ _ hd
    (G.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton t) hγ
    (FrobeniusModule.ne_zero_of_hasEigenvalue hγ)
  simp only [Scheme.Hom.residueCard, map_pow, norm_pow]
  exact (pow_le_natCast_pow_rpow_iff (norm_nonneg _) _ hd _).2 (h β hβ)

/-- On a scheme with a single point, quasi-finite over `k₀`, purity of weight `v` of `H_c^0`
(relative to `q = #k₀`) gives punctual purity of weight `v`. -/
theorem WeilSheaf.isPunctuallyPureOfWeight_of_compactlySupportedCohomology_zero {v : ℝ}
    (h : (G.compactlySupportedCohomology 0).IsPureOfWeightOver k₀ ι v) :
    G.IsPunctuallyPureOfWeight ι v := by
  intro t γ hγ
  have hd := Scheme.Hom.degreeOver_ne_zero (T ↘ Spec (CommRingCat.of k₀)) t.2
  obtain ⟨β, hβ, rfl⟩ := LinearMap.exists_hasEigenvalue_pow_eq_of_charpolyRev_eq_expand _ _ hd
    (G.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton t) hγ
    (FrobeniusModule.ne_zero_of_hasEigenvalue hγ)
  simp only [Scheme.Hom.residueCard, map_pow, norm_pow]
  exact (pow_eq_natCast_pow_rpow_iff (norm_nonneg _) _ hd _).2 (h β hβ)

/-- On a scheme with a single point, quasi-finite over `k₀`, if `H_c^0` is `ι`-real then so is
the Weil sheaf: the local polynomial of `H_c^0` is the expansion `det (1 - T^d F_t)`. -/
theorem WeilSheaf.isReal_of_compactlySupportedCohomology_zero
    (h : (G.compactlySupportedCohomology 0).IsReal ι) : G.IsReal ι := by
  intro t
  rw [FrobeniusModule.IsReal, FrobeniusModule.localPolynomial,
    G.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton t] at h
  exact (Polynomial.forall_coeff_expand_fixed_iff ι _
    (Scheme.Hom.degreeOver_ne_zero _ t.2) _).1 h

end CompactlySupportedCohomology

end AlgebraicGeometry
