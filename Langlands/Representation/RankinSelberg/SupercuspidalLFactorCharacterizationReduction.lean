import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.PairLFactorCharacterizationStatement
import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleStatement
import Langlands.Representation.Classification.SupercuspidalTemperedQuotientSingleBlockStatement

/-!
# Henniart 2002, Théorème 1.6(b), from its inputs

The characterization of supercuspidal representations by L-factors of pairs,
derived from JPSS 1983, (8.1)(i) and (9.4)(3), the one-block form of
supercuspidal Langlands quotients, and the pole statement for twisted tempered
blocks.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalLFactorCharacterization

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- (i) ⇒ (ii): for irreducible supercuspidal `π` of `GL_(n+1)(F)` and `ρ` of
`GL_(r+1)(F)`, `r < n`, the L-factor of the pair through the Langlands
classification is `1`. -/
theorem isLanglandsPairLPolynomial_one_of_isSupercuspidal
    (h81 : SupercuspidalUnequalRankLFactorStatement.{uF, max uF uV, max uF uW})
    (hS1V : Classification.SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uV})
    (hS1W : Classification.SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n r : ℕ) (hr : r < n)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (ρ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (hπ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible π.representation)
    (hπsc : letI := F.canonicalTopologicalData.topology
      GeneralLinear.IsSupercuspidal π.representation)
    (hρ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible ρ.representation)
    (hρsc : letI := F.canonicalTopologicalData.topology
      GeneralLinear.IsSupercuspidal ρ.representation) :
    IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π ρ 1 := by
  let _ := F.canonicalTopologicalData.topology
  refine ⟨exists_temperedLanglandsDatum_isLanglandsQuotient F _ (n + 1) n.succ_pos π hπ,
    exists_temperedLanglandsDatum_isLanglandsQuotient F _ (r + 1) r.succ_pos ρ hρ, ?_⟩
  intro d e hd he
  obtain ⟨φ⟩ := d.nonempty_standardModule_equiv_of_length_eq_one
    (hS1V p F _ n d π hd hπsc) π hd
  obtain ⟨φ'⟩ := e.nonempty_standardModule_equiv_of_length_eq_one
    (hS1W p F _ r e ρ he hρsc) ρ he
  have h1 := h81 p F ψ ν n r π.representation ρ.representation hπ hπsc
    (isOfWhittakerType_of_isSupercuspidal F ψ r ρ hρ hρsc) hr
  exact (IsPadicSymmetricLPolynomial.congr_equiv φ φ').mpr
    ((isPadicSymmetricLPolynomial_of_le hr.le).mpr h1)

/-- A one-block Langlands quotient with a supercuspidal block is supercuspidal. -/
theorem isSupercuspidal_of_length_eq_one {n : ℕ}
    (d : PadicField.TopologicalData.TemperedLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData n)
    (hB : d.shape.length = 1) (i : Fin d.shape.length)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear n F.Carrier))
    (hd : d.IsLanglandsQuotient π)
    (hsc : letI := F.canonicalTopologicalData.topology
      GeneralLinear.IsSupercuspidal (d.blocks i).representation) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear.IsSupercuspidal π.representation := by
  let _ := F.canonicalTopologicalData.topology
  obtain ⟨φ⟩ := d.nonempty_standardModule_equiv_of_length_eq_one hB π hd
  refine GeneralLinear.isSupercuspidal_of_equiv
    ((singleBlockStandardModuleEquiv F d hB i).symm.trans φ) ?_
  refine (isSupercuspidal_comp_reindex_iff F _ _).mpr ?_
  exact (GeneralLinear.isSupercuspidal_twist_iff _
    (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter _ _)
    (F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter _ _)
    _).mpr hsc

/-- The first block of a Langlands datum of a non-supercuspidal irreducible
representation of `GL_(n+2)(F)`: either it is one of at least two blocks, or it
is the only block and is not supercuspidal. -/
theorem size_le_or_not_isSupercuspidal {n : ℕ}
    (d : PadicField.TopologicalData.TemperedLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (n + 2))
    (i : Fin d.shape.length)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 2) F.Carrier))
    (hd : d.IsLanglandsQuotient π)
    (hnsc : ¬ (letI := F.canonicalTopologicalData.topology
      GeneralLinear.IsSupercuspidal π.representation)) :
    d.shape.size i ≤ n + 1 ∨
      (d.shape.size i = n + 2 ∧ ¬ (letI := F.canonicalTopologicalData.topology
        GeneralLinear.IsSupercuspidal (d.blocks i).representation)) := by
  by_cases hB : d.shape.length = 1
  · exact Or.inr ⟨d.shape.singleBlock_size hB i,
      fun hsc => hnsc (isSupercuspidal_of_length_eq_one F d hB i π hd hsc)⟩
  · left
    have hlen : 2 ≤ d.shape.length := by
      have := i.isLt
      omega
    obtain ⟨j, hij⟩ : ∃ j : Fin d.shape.length, i ≠ j := by
      by_cases h0 : (i : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    have hsum : ∑ k ∈ ({i, j} : Finset (Fin d.shape.length)), d.shape.size k ≤
        ∑ k, d.shape.size k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hij, d.shape.sum_eq] at hsum
    have := d.shape.positive j
    omega

/-- (ii) ⇒ (i): if `L(s, π × ρ) = 1` for every irreducible supercuspidal `ρ` of
`GL_(r+1)(F)`, `r ≤ n`, then the irreducible representation `π` of
`GL_(n+2)(F)` is supercuspidal. -/
theorem isSupercuspidal_of_forall_isLanglandsPairLPolynomial
    (h94 : LanglandsTypeLFactorStatement.{uF, uV, uW})
    (hS1W : Classification.SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uW})
    (hS2 : TemperedTwistSupercuspidalPoleStatement.{uF, uV, max uF uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (n + 2) F.Carrier))
    (hπ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible π.representation)
    (hall : ∀ (r : ℕ), r ≤ n →
      ∀ ρ : letI := F.canonicalTopologicalData.topology
          SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier),
        (letI := F.canonicalTopologicalData.topology;
          Representation.IsIrreducible ρ.representation) →
        (letI := F.canonicalTopologicalData.topology;
          GeneralLinear.IsSupercuspidal ρ.representation) →
        IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π ρ 1) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear.IsSupercuspidal π.representation := by
  let _ := F.canonicalTopologicalData.topology
  by_contra hnsc
  obtain ⟨d, hd⟩ :=
    exists_temperedLanglandsDatum_isLanglandsQuotient F _ (n + 2) (by omega) π hπ
  have hlen : 0 < d.shape.length := by
    by_contra h0
    have hsum := d.shape.sum_eq
    have : IsEmpty (Fin d.shape.length) := ⟨fun k => by have := k.isLt; omega⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    omega
  let i : Fin d.shape.length := ⟨0, hlen⟩
  obtain ⟨r, ρ, P, hρ, hρsc, hle, hlt, hP, hroot⟩ :=
    hS2 p F ψ ν (d.shape.size i) (d.blocks i) (d.exponent i) (d.shape.positive i)
      (d.irreducible i) (d.tempered i)
  have hrn : r ≤ n := by
    rcases size_le_or_not_isSupercuspidal F d i π hd hnsc with h | ⟨h, hτ⟩
    · omega
    · have := hlt hτ
      omega
  obtain ⟨-, ⟨e, he⟩, hall'⟩ := hall r hrn ρ hρ hρsc
  have he1 : e.shape.length = 1 := hS1W p F _ r e ρ he hρsc
  obtain ⟨P', Q, hP', hQ, hprod⟩ := h94 p F ψ ν (n + 1) r d e
  have h1 : P' = 1 := hP'.unique (hall' d e hd he)
  let j : Fin e.shape.length := ⟨0, by omega⟩
  have hQ1 : Q i j = 1 := by
    have hdvd : Q i j ∣ 1 := by
      rw [← h1, hprod]
      exact (Finset.dvd_prod_of_mem (fun j' => Q i j') (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i' => ∏ j', Q i' j') (Finset.mem_univ i))
    obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    have h0 := IsPadicRankLPolynomial.coeff_zero' F (hQ i j)
    rw [← hc, Polynomial.coeff_C_zero] at h0
    rw [← hc, h0, map_one]
  obtain ⟨φ'⟩ := e.nonempty_standardModule_equiv_of_length_eq_one he1 ρ he
  have hQρ := (isPadicRankLPolynomial_comp_reindex_iff F
    (e.shape.singleBlock_size he1 j) _ _).mpr (hQ i j)
  rw [isPadicRankLPolynomial_congr_right F _
    ((singleBlockStandardModuleEquiv F e he1 j).symm.trans φ')] at hQρ
  have hPQ : P = Q i j := hP.unique hQρ
  rw [hPQ, hQ1] at hroot
  simp at hroot

/-- Henniart 2002, Théorème 1.6(b), (i) ⇔ (ii), from JPSS (8.1)(i), JPSS (9.4)(3),
the one-block form of supercuspidal Langlands quotients and the pole statement for
twisted tempered blocks. -/
theorem supercuspidalLFactorCharacterization_of
    (h81 : SupercuspidalUnequalRankLFactorStatement.{uF, max uF uV, max uF uW})
    (h94 : LanglandsTypeLFactorStatement.{uF, uV, uW})
    (hS1V : Classification.SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uV})
    (hS1W : Classification.SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uW})
    (hS2 : TemperedTwistSupercuspidalPoleStatement.{uF, uV, max uF uW}) :
    SupercuspidalLFactorCharacterizationStatement.{uF, uV, uW} := by
  intro p _ F ψ ν n π hπ _
  constructor
  · intro hπsc r hr ρ hρ hρsc
    exact isLanglandsPairLPolynomial_one_of_isSupercuspidal F h81 hS1V hS1W ψ ν (n + 1) r
      (by omega) π ρ hπ hπsc hρ hρsc
  · exact isSupercuspidal_of_forall_isLanglandsPairLPolynomial F h94 hS1W hS2 ψ ν n π hπ

end Langlands.RankinSelberg.SupercuspidalLFactorCharacterization
