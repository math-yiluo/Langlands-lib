import Langlands.Representation.RankinSelberg.UnitarySupercuspidalEuler
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.SupercuspidalProductGamma

/-! # Actual finite Euler data for supercuspidal pairs of arbitrary ranks -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Contragredience includes the equality of the two positive ranks and
transport of the original first action along that equality. -/
def IsRankContragredient {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) : Prop :=
  ∃ h : r = n,
    letI := F.canonicalTopologicalData.topology
    haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
    Nonempty ((h ▸ π).Equiv (smoothContragredient σ))

/-- An actual finite unitary Euler datum with a symmetric pair certificate
and an exact test for a pole at zero. -/
structure SupercuspidalPairEuler
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) where
  data : LocalFactor.FiniteUnitaryEuler
  q_eq : data.q = F.canonicalTopologicalData.residueCardinality
  certified : IsPadicSymmetricLPolynomial F ψ ν.val π σ data.polynomial
  one_mem_iff : (1 : ℂ) ∈ data.parameters ↔ IsRankContragredient π σ

/-- Construct Euler data for arbitrary ranks. The unequal-rank formula and
supercuspidal genericity are discharged by published proofs. -/
def supercuspidalPairEuler
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hiπ : π.IsIrreducible) (hiσ : σ.IsIrreducible)
    (hsπ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π)
    (hsσ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal σ)
    (huπ : IsUnitarizable π) (huσ : IsUnitarizable σ) :
    SupercuspidalPairEuler ψ ν π σ := by
  classical
  let := F.canonicalTopologicalData.topology
  have hwπ := isOfWhittakerType_of_supercuspidalKirillov
    (ψ := ψ) Langlands.supercuspidalKirillov hsπ hiπ
  have hwσ := isOfWhittakerType_of_supercuspidalKirillov
    (ψ := ψ) Langlands.supercuspidalKirillov hsσ hiσ
  by_cases he : r = n
  · subst n
    let U := unitaryContragredientTwistParameterSet F π σ
      hiπ hiσ hsπ.1 hsσ.1 huπ huσ
    refine ⟨U.eulerData, rfl, ?_, ?_⟩
    · exact (isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mpr
        (U.isPadicPairLPolynomial hEq ν hiπ hsπ hiσ hwσ)
    · simpa [IsRankContragredient] using U.one_mem_iff
  · let E : LocalFactor.FiniteUnitaryEuler :=
      ⟨F.canonicalTopologicalData.residueCardinality,
        by exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one,
        ∅, by simp⟩
    refine ⟨E, rfl, ?_, ?_⟩
    · have hE : E.polynomial = 1 := by
        simp [E, LocalFactor.FiniteUnitaryEuler.polynomial]
      rw [hE]
      by_cases hle : n ≤ r
      · exact (isPadicSymmetricLPolynomial_of_le hle).mpr
          (supercuspidalUnequalRankLFactor p F ψ ν r n π σ hiπ hsπ hwσ (by omega))
      · exact (isPadicSymmetricLPolynomial_of_lt (by omega)).mpr
          (supercuspidalUnequalRankLFactor p F ψ ν n r σ π hiσ hsσ hwπ (by omega))
    · constructor
      · intro h
        simp [E] at h
      · rintro ⟨h, _⟩
        exact (he h).elim

namespace SupercuspidalPairEuler

variable {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
  {r n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  (D : SupercuspidalPairEuler ψ ν π σ)

/-- Every certified polynomial has the same actual spectral reciprocal. -/
theorem reciprocal_eq_of_certified {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P) (s : ℂ) :
    D.data.reciprocal s =
      (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s))⁻¹ := by
  rw [hP.unique D.certified]
  change (D.data.denominator s)⁻¹ = _
  rw [D.data.denominator_eq_eval]
  congr 2
  have hq : 0 < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast lt_trans Nat.zero_lt_one
      F.canonicalTopologicalData.residueCardinality_gt_one
  simpa only [D.q_eq] using
    (spectralPoint_eq_spectralParameter _ hq s).symm

end SupercuspidalPairEuler

end Langlands.RankinSelberg
