import Langlands.Global.RankinSelberg.EqualEulerPointwise
import Langlands.Automorphic.Unramified.WeakInductionPairEuler
import Langlands.Automorphic.Unramified.IsobaricArithmeticSpectralTransport
import Langlands.Global.Factors.HeckeEulerProduct

/-! # Pair Euler factors of weak induction with isobaric base change -/

noncomputable section

set_option autoImplicit false

open scoped NumberField

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Filter Polynomial
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.Automorphic.CuspidalOperatorRealization

private theorem spectralPoint_residueCardinality_above
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : FinitePlace F) (w : FinitePlacesAbove E v) (z : ℂ) :
    RankinSelberg.spectralPoint (residueCardinality w.1) z =
      RankinSelberg.spectralPoint (residueCardinality v) z ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
  unfold residueCardinality
  rw [Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise.residueCardinality_canonical w.1, ← Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal,
    ← Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise.residueCardinality_canonical v]
  simp only [RankinSelberg.spectralPoint, Nat.cast_pow, ← Complex.cpow_nat_mul,
    Complex.natCast_cpow_natCast_mul]

private theorem comp_prod {ι : Type*} (s : Finset ι) (P : ι → ℂ[X]) (Q : ℂ[X]) :
    (∏ i ∈ s, P i).comp Q = ∏ i ∈ s, (P i).comp Q :=
  map_prod (Polynomial.compRingHom Q) P s

private theorem pairEulerPolynomial_eq_prod_comp_left {n m : ℕ} (a : Fin n → ℂˣ)
    (b : Eigenvalues m) :
    pairEulerPolynomial (Eigenvalues.ofTuple a) b =
      ∏ i, b.eulerPolynomial.comp (C (a i : ℂ) * X) := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective m b
  rw [pairEulerPolynomial_ofTuple, Eigenvalues.eulerPolynomial_ofTuple]
  simp only [comp_prod, sub_comp, one_comp, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
    mul_comm ((z _ : ℂ)) ((a _ : ℂ))]

private theorem pairEulerPolynomial_congr_right {n m k : ℕ} (a : Eigenvalues n)
    {b : Eigenvalues m} {b' : Eigenvalues k} (h : b.eulerPolynomial = b'.eulerPolynomial) :
    pairEulerPolynomial a b = pairEulerPolynomial a b' := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n a
  rw [pairEulerPolynomial_eq_prod_comp_left, pairEulerPolynomial_eq_prod_comp_left, h]

private theorem pairEulerPolynomial_finiteSum_right {ι : Type*} [Fintype ι]
    {n : ℕ} {m : ι → ℕ} (a : Eigenvalues n) (b : ∀ i, Eigenvalues (m i)) :
    pairEulerPolynomial a (Eigenvalues.finiteSum b) = ∏ i, pairEulerPolynomial a (b i) := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n a
  simp_rw [pairEulerPolynomial_eq_prod_comp_left, Eigenvalues.eulerPolynomial_finiteSum, comp_prod]
  exact Finset.prod_comm

private theorem cast_sameEulerPolynomials {I : Type*} {n m : ℕ} (h : n = m)
    (s : SpectralSystem I n) :
    (h ▸ s : SpectralSystem I m).SameEulerPolynomials s :=
  Filter.Eventually.of_forall fun v hv hv' => SpectralSystem.eulerPolynomial_eqRec h s v hv hv'

private theorem presentation_sameEulerPolynomials {K : Type*} [Field K] [NumberField K]
    [CompactSpace (AdeleQuotient K)] {r : ℕ} {S : CuspidalOperatorRealization K r}
    (P : CuspidalSpectralPresentation S) {s : SpectralSystem (FinitePlace K) (r + 1)}
    (hs : IsoClass.HasSpectralSystem S.isoClass s) :
    s.SameEulerPolynomials P.spectralSystem := by
  exact Filter.Eventually.of_forall fun v hv hv' => congrArg Eigenvalues.eulerPolynomial
    (hs.eigenvalues_eq ⟨S, P, rfl, rfl⟩ v hv hv')

/-- At almost every finite place, the pair Euler factor of a supplied weak
induction and a second cuspidal representation is the product of the upper
pair factors with the constituents of a supplied isobaric weak base change
of the second representation. The identity holds for the specified actual
presentations. Upper places are grouped over the chosen base place. -/
def WeakInductionPairEulerValuesStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r r' m k : ℕ) (d : Fin k → ℕ)
    (S : CuspidalOperatorRealization F r) (S' : CuspidalOperatorRealization F r')
    (T : CuspidalOperatorRealization E m) (U : ∀ i, CuspidalOperatorRealization E (d i))
    (P : CuspidalSpectralPresentation.{uF, uV} S)
    (P' : CuspidalSpectralPresentation.{uF, uV} S')
    (Q : CuspidalSpectralPresentation.{uE, uW} T)
    (Q' : ∀ i, CuspidalSpectralPresentation.{uE, uW} (U i)),
    IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass →
    IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
      (Finset.univ.val.map fun i => PositiveRankCuspidalClass.ofFixedRank (U i).isoClass)
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S'.isoClass)) →
    ∀ᶠ v : FinitePlace F in cofinite,
      ∃ (hv : v ∉ P.exceptional) (hv' : v ∉ P'.exceptional)
        (hw : ∀ w : FinitePlacesAbove E v, w.1 ∉ Q.exceptional)
        (hw' : ∀ (i : Fin k) (w : FinitePlacesAbove E v), w.1 ∉ (Q' i).exceptional),
      ∀ z : ℂ,
        ((pairEulerPolynomial (P.spectralSystem.eigenvalues v hv)
          (P'.spectralSystem.eigenvalues v hv')).eval
            (RankinSelberg.spectralPoint (residueCardinality v) z))⁻¹ =
        ∏ w : FinitePlacesAbove E v, ∏ i : Fin k,
          ((pairEulerPolynomial (Q.spectralSystem.eigenvalues w.1 (hw w))
            ((Q' i).spectralSystem.eigenvalues w.1 (hw' i w))).eval
              (RankinSelberg.spectralPoint (residueCardinality w.1) z))⁻¹

set_option maxHeartbeats 600000 in
theorem weakInductionPairEulerValues :
    WeakInductionPairEulerValuesStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ r r' m k d S S' T U P P' Q Q' hInd hBC
  obtain ⟨s, t, hs, ht, hst⟩ := hInd
  have hInd' := hst.of_sameEulerPolynomials
    (presentation_sameEulerPolynomials P hs) (presentation_sameEulerPolynomials Q ht)
  obtain ⟨h, b, b', hb, hb', hbb'⟩ := hBC
  obtain ⟨b₀, hb₀, hb₀b⟩ := hb.exists_ofCuspidal
  let upperSystems i := (Q' i).spectralSystem
  let upperSum := SpectralSystem.finiteSum upperSystems
  have hRank : (∑ i, (d i + 1)) =
      IsobaricData.rank
        (Finset.univ.val.map fun i => PositiveRankCuspidalClass.ofFixedRank (U i).isoClass) := by
    rw [IsobaricData.rank_eq_sum, Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  have hSameCast := cast_sameEulerPolynomials hRank upperSum
  have hSum : IsobaricData.HasSpectralSystem.{uE, uW}
      (Finset.univ.val.map fun i => PositiveRankCuspidalClass.ofFixedRank (U i).isoClass)
      (hRank ▸ upperSum) :=
    ⟨k, fun i => PositiveRankCuspidalClass.ofFixedRank (U i).isoClass, rfl,
      upperSystems, fun i => ⟨U i, Q' i, rfl, rfl⟩, hSameCast.symm⟩
  have hRank' : (∑ i, (d i + 1)) = r' + 1 := hRank.trans h
  let upperCast := (hRank' ▸ upperSum : SpectralSystem (FinitePlace E) (r' + 1))
  have hCast : upperCast.SameEulerPolynomials upperSum :=
    cast_sameEulerPolynomials hRank' upperSum
  let witnessCast := (h ▸ b' : SpectralSystem (FinitePlace E)
    (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S'.isoClass)).rank)
  have hUpper : witnessCast.SameEulerPolynomials upperCast :=
    (cast_sameEulerPolynomials h b').trans
      ((hb'.sameEulerPolynomials hSum).trans (hSameCast.trans hCast.symm))
  have hBC' : upperCast.IsArithmeticWeakBaseChangeOf P'.spectralSystem :=
    hbb'.of_sameEulerPolynomials
    (hb₀b.symm.trans (presentation_sameEulerPolynomials P' hb₀)) hUpper
  filter_upwards [weakInductionPairEuler F E (r + 1) (m + 1) (r' + 1)
    P.spectralSystem Q.spectralSystem P'.spectralSystem upperCast hInd' hBC'] with v hv
  obtain ⟨hP, hP', hQ, hu, he⟩ := hv
  have hu' (w : FinitePlacesAbove E v) :
      w.1 ∉ SpectralSystem.familyExceptional upperSystems := by
    simpa only [upperCast, SpectralSystem.exceptional_eqRec, upperSum, SpectralSystem.finiteSum]
      using hu w
  refine ⟨hP, hP', hQ, fun i w => SpectralSystem.not_mem_exceptional upperSystems w.1 (hu' w) i,
    fun z => ?_⟩
  erw [he]
  rw [eval_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hPoly : (upperCast.eigenvalues w.1 (hu w)).eulerPolynomial =
      (upperSum.eigenvalues w.1 (hu' w)).eulerPolynomial :=
    SpectralSystem.eulerPolynomial_eqRec hRank' upperSum w.1 (hu w) (hu' w)
  rw [eval_comp, eval_pow, eval_X, ← spectralPoint_residueCardinality_above v w z,
    pairEulerPolynomial_congr_right _ hPoly]
  change ((pairEulerPolynomial (Q.spectralSystem.eigenvalues w.1 (hQ w))
    (Eigenvalues.finiteSum fun i =>
      (upperSystems i).eigenvalues w.1 (SpectralSystem.not_mem_exceptional _ _ (hu' w) i))).eval
        (RankinSelberg.spectralPoint (residueCardinality w.1) z))⁻¹ = _
  rw [pairEulerPolynomial_finiteSum_right, eval_prod, ← Finset.prod_inv_distrib]

end Langlands.Automorphic.Unramified
