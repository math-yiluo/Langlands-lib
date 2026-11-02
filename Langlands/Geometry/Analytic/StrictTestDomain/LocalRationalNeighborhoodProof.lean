import Langlands.Geometry.Analytic.StrictTestDomain.LocalRationalNeighborhoodStatement
import Langlands.Geometry.Analytic.StrictTestDomain.FibreComparison
import Langlands.Geometry.Analytic.StrictTestDomain.LyingOver
import Langlands.Geometry.Analytic.StrictTestDomain.ApproximateFiniteness
import Langlands.Geometry.Analytic.StrictTestDomain.QuotientTests
import Langlands.Geometry.Analytic.StrictTestDomain.RationalRestriction
import Langlands.Geometry.Analytic.StrictTestDomain.RationalNeighborhoodBasis
import Langlands.Geometry.Analytic.StrictTestDomain.RationalTensorComparison
import Langlands.Geometry.Analytic.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.Spectrum.Nonarchimedean
import Langlands.Analysis.NonarchimedeanCompletedTensorProof

/-! # Local rational neighbourhoods of strictly represented subsets: proof -/

noncomputable section

universe u

namespace Langlands.Analytic

open Topology

namespace PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- The bounded equivalence induced by an equality of presentations matches
the coordinates. -/
theorem equivOfEq_coordinate {P Q : PresentedStrictAffinoidAlgebra K} (h : P = Q)
    (hk : P.arity = Q.arity) (k : Fin P.arity) :
    equivOfEq K h (coordinate K P k) = coordinate K Q (Fin.cast hk k) := by
  subst h
  rfl

end PresentedStrictAffinoidAlgebra

section Scalars

variable {K : Type u} [NormedField K]

namespace BanachSpectrum

/-- Scalars act on spectrum values through their norms. -/
theorem apply_smul {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    (x : BanachSpectrum A) (c : K) (a : A) : x (c • a) = ‖c‖ * x a := by
  rw [Algebra.smul_def, map_mul, BanachSpectrum.algebraMap_apply]

end BanachSpectrum


end Scalars

namespace StrictTestDomain

open BanachSpectrum PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Lying over for finite bounded maps of presented strict affinoid algebras over
a field with an element of norm greater than one. -/
theorem exists_comap_eq_of_finite_of_one_lt (hK : ∃ c : K, 1 < ‖c‖)
    {A B : PresentedStrictAffinoidAlgebra K} (φ : BoundedAlgHom K A B)
    (hfin : φ.toAlgHom.toRingHom.Finite) (x : BanachSpectrum A)
    (hx : RingHom.ker φ.toAlgHom.toRingHom ≤ x.kernel) :
    ∃ y : BanachSpectrum B, comap φ.toBoundedRingHom y = x := by
  let _ : NontriviallyNormedField K := { ‹NormedField K› with non_trivial := hK }
  exact BanachSpectrum.exists_comap_eq_of_finite φ hfin x hx

namespace RationalData

variable {P Q : PresentedStrictAffinoidAlgebra K}

/-- The old coordinates of a rational quotient are the images of the
coordinates of the base. -/
theorem coordinate_castAdd (d : RationalData K P) (k : Fin P.arity) :
    coordinate K d.algebra (Fin.castAdd d.arity k) = d.baseMap (coordinate K P k) := by
  have h1 : (RationalLocalization.modelEquiv K P).symm (coordinate K P k) =
      coordinate K (RationalLocalization.model K P) k := by
    have h2 := equivOfEq_coordinate (ofRelations_ideal K P) rfl k
    change RationalLocalization.modelEquiv K P
      (coordinate K (RationalLocalization.model K P) k) = coordinate K P k at h2
    rw [← h2, BoundedAlgEquiv.symm_apply_apply]
  change _ = RationalPresentation.baseMap K P.arity d.arity P.ideal
      (RationalLocalization.seriesLift K P d.denominator)
      (fun j => RationalLocalization.seriesLift K P (d.numerator j))
      ((RationalLocalization.modelEquiv K P).symm (coordinate K P k))
  rw [h1]
  exact (RationalPresentation.baseMap_coordinate K P.arity d.arity _ _ _ k).symm

/-- The new coordinates of a rational quotient are its fraction coordinates. -/
theorem coordinate_natAdd (d : RationalData K P) (j : Fin d.arity) :
    coordinate K d.algebra (Fin.natAdd P.arity j) = d.fraction j := rfl

/-- **Finiteness on an approximating rational domain.** Suppose that on the
locus of `d` the element `g` does not vanish and dominates every `f k`, and that
at every point of `M(Q)` over the locus of `d` the fractions `i (f k) / i g`
approximate the coordinates of `Q` to within less than one. Then the comparison
map of `d` is finite. -/
theorem finite_comparison_of_approx (hK : ∃ c : K, 1 < ‖c‖) (i : BoundedAlgHom K P Q)
    (d : RationalData K P) (g : P) (f : Fin Q.arity → P)
    (hd : ∀ x' ∈ d.locus, 0 < x' g ∧ ∀ k, x' (f k) ≤ x' g)
    (hy : ∀ y' : BanachSpectrum Q, comap i.toBoundedRingHom y' ∈ d.locus →
      ∀ k, y' (i g * coordinate K Q k - i (f k)) < y' (i g)) :
    (d.comparison i).toAlgHom.toRingHom.Finite := by
  classical
  have hbase : ∀ a : P, d.comparison i (d.baseMap a) = (d.pullback i).baseMap (i a) :=
    fun a => congrArg (fun χ : BoundedAlgHom K P (d.pullback i).algebra => χ a)
      (d.comparison_comp_baseMap i)
  have hg : ∀ x₃ : BanachSpectrum d.algebra, 0 < x₃ (d.baseMap g) := fun x₃ =>
    (hd _ (d.comap_baseMap_mem_locus x₃)).1
  have hunit : IsUnit (d.baseMap g) :=
    (isUnit_iff_forall_spectrum_ne_zero d.algebra _).mpr fun x₃ => (hg x₃).ne'
  obtain ⟨v, hv⟩ : ∃ v : d.algebra, v * d.baseMap g = 1 :=
    ⟨↑hunit.unit⁻¹, hunit.val_inv_mul⟩
  let a : Fin (Q.arity + d.arity) → d.algebra :=
    Fin.addCases (fun k => d.baseMap (f k) * v) (fun j => d.fraction j)
  have hak : ∀ k, a (Fin.castAdd d.arity k) * d.baseMap g = d.baseMap (f k) := by
    intro k
    simp only [a, Fin.addCases_left]
    rw [mul_assoc, hv, mul_one]
  have ha : ∀ (x₃ : BanachSpectrum d.algebra) (k : Fin (Q.arity + d.arity)),
      x₃ (a k) ≤ 1 := by
    intro x₃ k
    refine Fin.addCases (m := Q.arity) (n := d.arity) (motive := fun k => x₃ (a k) ≤ 1)
      (fun k => ?_) (fun j => ?_) k
    · have hmul : x₃ (a (Fin.castAdd d.arity k)) * x₃ (d.baseMap g) =
          x₃ (d.baseMap (f k)) := by
        rw [← map_mul x₃.toMulRingSeminorm, hak k]
      have hle : x₃ (d.baseMap (f k)) ≤ x₃ (d.baseMap g) :=
        (hd _ (d.comap_baseMap_mem_locus x₃)).2 k
      rw [← hmul] at hle
      exact (mul_le_iff_le_one_left (hg x₃)).mp hle
    · simp only [a, Fin.addCases_right]
      exact (x₃.le_norm _).trans (norm_coordinate_le_one d.algebra (Fin.natAdd P.arity j))
  have hcomap : ∀ y₃ : BanachSpectrum (d.pullback i).algebra,
      comap i.toBoundedRingHom (comap (d.pullback i).baseMap.toBoundedRingHom y₃) =
        comap d.baseMap.toBoundedRingHom (comap (d.comparison i).toBoundedRingHom y₃) := by
    intro y₃
    apply BanachSpectrum.ext
    intro b
    change y₃ ((d.pullback i).baseMap (i b)) = y₃ (d.comparison i (d.baseMap b))
    rw [hbase]
  have hc : ∀ (y₃ : BanachSpectrum (d.pullback i).algebra) (k : Fin (Q.arity + d.arity)),
      y₃ (coordinate K (d.pullback i).algebra k - d.comparison i (a k)) < 1 := by
    intro y₃ k
    refine Fin.addCases (m := Q.arity) (n := d.arity) (motive := fun k =>
      y₃ (coordinate K (d.pullback i).algebra k - d.comparison i (a k)) < 1)
      (fun k => ?_) (fun j => ?_) k
    · have hcc : coordinate K (d.pullback i).algebra (Fin.castAdd d.arity k) =
          (d.pullback i).baseMap (coordinate K Q k) :=
        coordinate_castAdd (d.pullback i) k
      have hy' : y₃ ((d.pullback i).baseMap (i g * coordinate K Q k - i (f k))) <
          y₃ ((d.pullback i).baseMap (i g)) :=
        hy (comap (d.pullback i).baseMap.toBoundedRingHom y₃)
          (by rw [hcomap]; exact d.comap_baseMap_mem_locus _) k
      have hpos : 0 < y₃ ((d.pullback i).baseMap (i g)) :=
        (apply_nonneg y₃.toMulRingSeminorm _).trans_lt hy'
      have hak3 : d.comparison i (a (Fin.castAdd d.arity k)) *
          (d.pullback i).baseMap (i g) = (d.pullback i).baseMap (i (f k)) := by
        rw [← hbase, ← hbase, ← map_mul (d.comparison i).toAlgHom, hak k]
      have hw : ((d.pullback i).baseMap (coordinate K Q k) -
          d.comparison i (a (Fin.castAdd d.arity k))) * (d.pullback i).baseMap (i g) =
            (d.pullback i).baseMap (i g * coordinate K Q k - i (f k)) := by
        rw [sub_mul, hak3, map_sub (d.pullback i).baseMap.toAlgHom,
          map_mul (d.pullback i).baseMap.toAlgHom]
        ring
      have h2 : y₃ ((d.pullback i).baseMap (coordinate K Q k) -
          d.comparison i (a (Fin.castAdd d.arity k))) *
            y₃ ((d.pullback i).baseMap (i g)) =
          y₃ ((d.pullback i).baseMap (i g * coordinate K Q k - i (f k))) := by
        rw [← map_mul y₃.toMulRingSeminorm, hw]
      rw [hcc]
      rw [← h2] at hy'
      exact (mul_lt_iff_lt_one_left hpos).mp hy'
    · simp only [a, Fin.addCases_right]
      change y₃ ((d.pullback i).fraction j - d.comparison i (d.fraction j)) < 1
      rw [d.comparison_fraction i j, sub_self, map_zero]
      exact zero_lt_one
  exact finite_of_spectrum_coordinate_sub_lt_one hK (d.comparison i) a ha hc

/-- **Approximating rational data.** Around a point `x` of a subset `U`
represented for strict tests, there are rational data `d` and elements `g, f k`
satisfying the hypotheses of `finite_comparison_of_approx`, such that the trace
of the locus of `d` on `U` is a neighbourhood of `x` in `U`. -/
theorem exists_approx_data
    (hT : Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u})
    (hK : ∃ c : K, 1 < ‖c‖) {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)}
    (hU : Represents K i U) {x : BanachSpectrum P} (hx : x ∈ U) :
    ∃ (d : RationalData K P) (g : P) (f : Fin Q.arity → P),
      (∀ x' ∈ d.locus, 0 < x' g ∧ ∀ k, x' (f k) ≤ x' g) ∧
      (∀ y' : BanachSpectrum Q, comap i.toBoundedRingHom y' ∈ d.locus →
        ∀ k, y' (i g * coordinate K Q k - i (f k)) < y' (i g)) ∧
      d.locus ∩ U ∈ 𝓝[U] x := by
  classical
  have hxr : x ∈ Set.range (comap i.toBoundedRingHom) := by
    rw [hU.2.1]
    exact hx
  obtain ⟨y, rfl⟩ := hxr
  obtain ⟨g, f, hg, hgf⟩ := exists_fraction_approximation hT hK hU y
    (fun k => coordinate K Q k) one_pos
  change 0 < y (i g) at hg
  have hgf' : ∀ k, y (i g * coordinate K Q k - i (f k)) < y (i g) := fun k => by
    have h := hgf k
    rw [one_mul] at h
    exact h
  obtain ⟨c, hc⟩ := hK
  have hc0 : 0 < ‖c‖ := zero_lt_one.trans hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hg (inv_lt_one_of_one_lt₀ hc)
  let a : K := c⁻¹ ^ n
  have ha : ‖a‖ = ‖c‖⁻¹ ^ n := by
    change ‖c⁻¹ ^ n‖ = _
    rw [norm_pow, norm_inv]
  have ha0 : 0 < ‖a‖ := by
    rw [ha]
    exact pow_pos (inv_pos.mpr hc0) n
  have hay : ‖a‖ < y (i g) := by
    rw [ha]
    exact hn
  -- The rational data making `g` large and dominating the numerators.
  let d₁ : RationalData K P :=
    { arity := Q.arity + 1
      denominator := g
      numerator := Fin.cons (algebraMap K P a) f
      no_common_zero := fun x' => Or.inr ⟨0, by
        rw [Fin.cons_zero, BanachSpectrum.algebraMap_apply]
        exact ha0.ne'⟩ }
  have hd₁ : ∀ x' : BanachSpectrum P,
      x' ∈ d₁.locus ↔ ‖a‖ ≤ x' g ∧ ∀ k, x' (f k) ≤ x' g := by
    intro x'
    change (∀ j, x' (Fin.cons (α := fun _ => Carrier K P) (algebraMap K P a) f j) ≤ x' g) ↔ _
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, BanachSpectrum.algebraMap_apply]
  -- The open set of points of `M(Q)` where the approximation is good.
  let G : Set (BanachSpectrum Q) := {y' | ‖a‖ < y' (i g)} ∩
    ⋂ k, {y' | y' (i g * coordinate K Q k - i (f k)) < y' (i g)}
  have hGo : IsOpen G :=
    (isOpen_lt continuous_const (BanachSpectrum.evaluation (i g)).continuous).inter
      (isOpen_iInter_of_finite fun k => isOpen_lt
        (BanachSpectrum.evaluation (i g * coordinate K Q k - i (f k))).continuous
        (BanachSpectrum.evaluation (i g)).continuous)
  have hyG : y ∈ G := ⟨hay, Set.mem_iInter.mpr hgf'⟩
  have hd₁G : ∀ y'' ∈ G, comap i.toBoundedRingHom y'' ∈ d₁.locus := by
    intro y'' hy''
    rw [hd₁]
    refine ⟨hy''.1.le, fun k => ?_⟩
    have hk := Set.mem_iInter.mp hy''.2 k
    change y'' (i (f k)) ≤ y'' (i g)
    have hle : y'' (i g * coordinate K Q k) ≤ y'' (i g) := by
      rw [map_mul y''.toMulRingSeminorm]
      exact mul_le_of_le_one_right (apply_nonneg _ _)
        ((y''.le_norm _).trans (norm_coordinate_le_one Q k))
    have hna := y''.isNonarchimedean (K := K) (i g * coordinate K Q k)
      (-(i g * coordinate K Q k - i (f k)))
    rw [map_neg_eq_map, ← sub_eq_add_neg, sub_sub_cancel] at hna
    exact hna.trans (max_le hle hk.le)
  -- Separate `x` from the image of the complement of `G`.
  have hZc : IsCompact (comap i.toBoundedRingHom '' Gᶜ) :=
    hGo.isClosed_compl.isCompact.image
      (BanachSpectrum.comapContinuous i.toBoundedRingHom).continuous
  have hinj := comap_injective_of_represents hT ⟨c, hc⟩ hU
  have hxZ : comap i.toBoundedRingHom y ∉ comap i.toBoundedRingHom '' Gᶜ := by
    rintro ⟨y'', hy'', heq⟩
    rw [hinj heq] at hy''
    exact hy'' hyG
  have hV : (comap i.toBoundedRingHom '' Gᶜ)ᶜ ∈ 𝓝 (comap i.toBoundedRingHom y) :=
    hZc.isClosed.isOpen_compl.mem_nhds hxZ
  obtain ⟨L, hLx, hLV⟩ := exists_locus_mem_nhds_subset ⟨c, hc⟩ _ hV
  have hG : ∀ y'' : BanachSpectrum Q, comap i.toBoundedRingHom y'' ∈ L.locus → y'' ∈ G := by
    intro y'' hy''
    by_contra hn
    exact hLV hy'' ⟨y'', hn, rfl⟩
  refine ⟨d₁.inter L, g, f, ?_, ?_, ?_⟩
  · intro x' hx'
    rw [locus_inter] at hx'
    obtain ⟨h1, h2⟩ := (hd₁ x').mp hx'.1
    exact ⟨ha0.trans_le h1, h2⟩
  · intro y' hy' k
    rw [locus_inter] at hy'
    exact Set.mem_iInter.mp (hG y' hy'.2).2 k
  · have hsub : U ∩ L.locus ⊆ (d₁.inter L).locus ∩ U := by
      rintro x'' ⟨hU', hL⟩
      refine ⟨?_, hU'⟩
      rw [locus_inter]
      refine ⟨?_, hL⟩
      have hxr : x'' ∈ Set.range (comap i.toBoundedRingHom) := by
        rw [hU.2.1]
        exact hU'
      obtain ⟨y'', rfl⟩ := hxr
      exact hd₁G y'' (hG y'' hL)
    exact Filter.mem_of_superset (inter_mem_nhdsWithin U hLx) hsub

/-- **Cutting out the represented subset.** If the comparison map of rational
data `d` for a map representing `U` is finite, then the trace of the locus of
`d` on `U` is itself the locus of rational data. -/
theorem exists_locus_eq_inter_of_finite (hK : ∃ c : K, 1 < ‖c‖)
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)} (hU : Represents K i U)
    (d : RationalData K P) (hfin : (d.comparison i).toAlgHom.toRingHom.Finite) :
    ∃ e : RationalData K P, e.locus = d.locus ∩ U := by
  classical
  have hU₃ := d.represents_comparison hU
  have hV : zeroLocus (RingHom.ker (d.comparison i).toAlgHom.toRingHom) ⊆
      comap d.baseMap.toBoundedRingHom ⁻¹' U := by
    intro x₃ hx₃
    obtain ⟨y₃, hy₃⟩ := exists_comap_eq_of_finite_of_one_lt hK (d.comparison i) hfin x₃ hx₃
    rw [← hU₃.2.1]
    exact ⟨y₃, hy₃⟩
  obtain ⟨e, he, -, hUe⟩ := exists_idempotent_of_zeroLocus_subset hK hU₃ hV
  have hunit : IsUnit (d.baseMap d.denominator) :=
    RationalLocalization.isUnit_baseMap_denominator K P d.arity d.denominator d.numerator
      d.generatesUnitIdeal
  have hden : ∀ x₃ : BanachSpectrum d.algebra, 0 < x₃ (d.baseMap d.denominator) :=
    fun x₃ => lt_of_le_of_ne (apply_nonneg _ _)
      ((isUnit_iff_forall_spectrum_ne_zero d.algebra _).mp hunit x₃).symm
  have hidem : ∀ x₃ : BanachSpectrum d.algebra, x₃ e < 1 → x₃ e = 0 := by
    intro x₃ h
    have h2 : x₃ e * x₃ e = x₃ e := by
      rw [← map_mul x₃.toMulRingSeminorm, he.eq]
    by_contra hne
    have h1 : x₃ e = 1 := mul_right_cancel₀ hne (h2.trans (one_mul _).symm)
    linarith
  obtain ⟨c, hc⟩ := hK
  have hc0 : 0 < ‖c‖ := zero_lt_one.trans hc
  have hρ0 : 0 < ‖c‖⁻¹ := inv_pos.mpr hc0
  have hρ1 : ‖c‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  obtain ⟨z, hz, hez⟩ := d.dense_fractionSubalgebra.exists_dist_lt e hρ0
  obtain ⟨r, q, hzq⟩ : ∃ r : ℕ, ∃ q : P,
      d.baseMap.toAlgHom d.denominator ^ r * z = d.baseMap.toAlgHom q := hz
  rw [dist_eq_norm] at hez
  have hzq' : d.baseMap d.denominator ^ (r + 1) * z = d.baseMap (d.denominator * q) := by
    rw [pow_succ', mul_assoc]
    change d.baseMap d.denominator * (d.baseMap d.denominator ^ r * z) = _
    rw [hzq, map_mul d.baseMap.toAlgHom]
  -- Spectral values of the approximation `z` of the idempotent `e`.
  have hval : ∀ x₃ : BanachSpectrum d.algebra,
      x₃ (d.baseMap d.denominator) ^ (r + 1) * x₃ z = x₃ (d.baseMap (d.denominator * q)) := by
    intro x₃
    rw [← map_pow x₃.toMulRingSeminorm, ← map_mul x₃.toMulRingSeminorm, hzq']
  have hez₃ : ∀ x₃ : BanachSpectrum d.algebra, x₃ (e - z) < ‖c‖⁻¹ := fun x₃ =>
    (x₃.le_norm _).trans_lt hez
  have hze₃ : ∀ x₃ : BanachSpectrum d.algebra, x₃ (z - e) < ‖c‖⁻¹ := fun x₃ => by
    rw [← neg_sub, map_neg_eq_map]
    exact hez₃ x₃
  have hzero : ∀ x₃ : BanachSpectrum d.algebra, x₃ e = 0 → x₃ z < ‖c‖⁻¹ := by
    intro x₃ h0
    have hna := x₃.isNonarchimedean (K := K) e (z - e)
    rw [add_sub_cancel, h0] at hna
    exact hna.trans_lt (max_lt hρ0 (hze₃ x₃))
  have hsmall : ∀ x₃ : BanachSpectrum d.algebra, x₃ z ≤ ‖c‖⁻¹ → x₃ e = 0 := by
    intro x₃ hz₃
    apply hidem
    have hna := x₃.isNonarchimedean (K := K) z (e - z)
    rw [add_sub_cancel] at hna
    exact hna.trans_lt (max_lt (hz₃.trans_lt hρ1) ((hez₃ x₃).trans hρ1))
  let e' : RationalData K P :=
    { arity := d.arity + 1
      denominator := d.denominator ^ (r + 1)
      numerator := Fin.cons (c • (d.denominator * q)) fun j => d.numerator j ^ (r + 1)
      no_common_zero := fun x' => by
        rcases d.no_common_zero x' with h | ⟨j, h⟩
        · left
          rw [map_pow]
          exact pow_ne_zero _ h
        · right
          refine ⟨j.succ, ?_⟩
          rw [Fin.cons_succ, map_pow]
          exact pow_ne_zero _ h }
  have hmem : ∀ x' : BanachSpectrum P, x' ∈ e'.locus ↔
      ‖c‖ * x' (d.denominator * q) ≤ x' d.denominator ^ (r + 1) ∧ x' ∈ d.locus := by
    intro x'
    change (∀ j, x' (Fin.cons (α := fun _ => Carrier K P) (c • (d.denominator * q))
        (fun j => d.numerator j ^ (r + 1)) j) ≤ x' (d.denominator ^ (r + 1))) ↔ _
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, map_pow,
      BanachSpectrum.apply_smul]
    exact and_congr Iff.rfl (forall_congr' fun j => pow_le_pow_iff_left₀
      (apply_nonneg _ _) (apply_nonneg _ _) (Nat.succ_ne_zero r))
  refine ⟨e', ?_⟩
  ext x'
  rw [hmem x']
  constructor
  · rintro ⟨hq, hx'⟩
    refine ⟨hx', ?_⟩
    rw [← d.range_comap_baseMap] at hx'
    obtain ⟨x₃, rfl⟩ := hx'
    change ‖c‖ * x₃ (d.baseMap (d.denominator * q)) ≤
      x₃ (d.baseMap d.denominator) ^ (r + 1) at hq
    rw [← hval] at hq
    have hD := pow_pos (hden x₃) (r + 1)
    have h4 : ‖c‖ * x₃ z ≤ 1 := by
      refine le_of_mul_le_mul_left ?_ hD
      calc x₃ (d.baseMap d.denominator) ^ (r + 1) * (‖c‖ * x₃ z)
          = ‖c‖ * (x₃ (d.baseMap d.denominator) ^ (r + 1) * x₃ z) := by ring
        _ ≤ x₃ (d.baseMap d.denominator) ^ (r + 1) := hq
        _ = x₃ (d.baseMap d.denominator) ^ (r + 1) * 1 := (mul_one _).symm
    have h3 : x₃ e = 0 := by
      apply hsmall
      rw [← mul_one ‖c‖⁻¹]
      exact (le_inv_mul_iff₀ hc0).mpr h4
    have hmemU : x₃ ∈ comap d.baseMap.toBoundedRingHom ⁻¹' U := by
      rw [hUe]
      exact h3
    exact hmemU
  · rintro ⟨hx', hxU⟩
    refine ⟨?_, hx'⟩
    rw [← d.range_comap_baseMap] at hx'
    obtain ⟨x₃, rfl⟩ := hx'
    have h3 : x₃ e = 0 := by
      have hmemU : x₃ ∈ comap d.baseMap.toBoundedRingHom ⁻¹' U := hxU
      rw [hUe] at hmemU
      exact hmemU
    have h5 : ‖c‖ * x₃ z ≤ 1 := by
      have h6 := mul_lt_mul_of_pos_left (hzero x₃ h3) hc0
      rw [mul_inv_cancel₀ hc0.ne'] at h6
      exact h6.le
    have hD := pow_pos (hden x₃) (r + 1)
    change ‖c‖ * x₃ (d.baseMap (d.denominator * q)) ≤ x₃ (d.baseMap d.denominator) ^ (r + 1)
    rw [← hval]
    calc ‖c‖ * (x₃ (d.baseMap d.denominator) ^ (r + 1) * x₃ z)
        = x₃ (d.baseMap d.denominator) ^ (r + 1) * (‖c‖ * x₃ z) := by ring
      _ ≤ x₃ (d.baseMap d.denominator) ^ (r + 1) * 1 :=
          mul_le_mul_of_nonneg_left h5 hD.le
      _ = x₃ (d.baseMap d.denominator) ^ (r + 1) := mul_one _

end RationalData

/-- **Local Gerritzen–Grauert for strict tests.** -/
theorem localRationalNeighborhood : LocalRationalNeighborhoodStatement.{u} := by
  intro K _ _ _ hK P Q i U hU x hx
  obtain ⟨d, g, f, hd, hy, hnhds⟩ :=
    RationalData.exists_approx_data Langlands.Analysis.nonarchimedeanCompletedTensor hK hU hx
  obtain ⟨e, he⟩ := RationalData.exists_locus_eq_inter_of_finite hK hU d
    (RationalData.finite_comparison_of_approx hK i d g f hd hy)
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    exact Set.inter_subset_right
  · rw [he]
    exact hnhds

end StrictTestDomain

end Langlands.Analytic
