import Langlands.BaseChange.NormTwistFibreReduction
import Langlands.BaseChange.PadicSquareIntegrableNotInduced
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.UnitaryContragredientTwistParameters
import Langlands.Representation.Unitary.Twist

/-! # Nonvanishing of a norm-twisted supercuspidal pair denominator -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory _root_.Polynomial RankinSelberg
open SupercuspidalLFactorCharacterization (isOfWhittakerType_of_isSupercuspidal)

universe u v uV

/-- A character trivial on the field norm has values of modulus one. -/
theorem IsNormTrivial.norm_eq_one {F : Type u} {E : Type v}
    [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {κ : Fˣ →* ℂˣ} (hκ : IsNormTrivial E κ) (x : Fˣ) : ‖(κ x : ℂ)‖ = 1 := by
  have hn : Units.map (Algebra.norm F : E →* F)
      (Units.map (algebraMap F E).toMonoidHom x) = x ^ Module.finrank F E := by
    apply Units.ext
    exact Algebra.norm_algebraMap (x : F)
  have hpow := hκ (Units.map (algebraMap F E).toMonoidHom x)
  rw [hn, map_pow] at hpow
  have h := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) hpow
  simp only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Module.finrank_pos.ne').mp h

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : Type v)
    [Field E] [Algebra F.Carrier E] [FiniteDimensional F.Carrier E]

local instance pairTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance pairGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

private theorem isUnitarizable_of_squareIntegrable {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hπ : F.canonicalTopologicalData.IsSquareIntegrable π) (hi : π.IsIrreducible) :
    IsUnitarizable π := by
  let T := F.canonicalTopologicalData
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  let := hμ
  have htop := (glBlockCentralQuotientTopology p F T n).1
  let := htop.2.1
  let := htop.2.2.1
  let := htop.2.2.2.1
  let := T.centralQuotientHaar_rightInvariant n μ
  let := Langlands.isInvInvariant_of_isMulRightInvariant μ
  obtain ⟨-, c, -⟩ := hπ μ
  exact HarishChandraSchwartz.isUnitarizable_of_isSquareIntegrable
    (Subgroup.center (GeneralLinear n F.Carrier)) le_rfl μ c.acts
    (GeneralLinear.compactOpen_cofinal F T n)
    ((isSquareIntegrableModCentralSubgroup_center_iff π μ).mpr (hπ μ)) hi

set_option maxHeartbeats 1600000 in
private theorem exists_normTwistedSupercuspidalSelfPairPolynomial
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hiπ : π.IsIrreducible) (hsπ : IsSupercuspidal π)
    (hqπ : F.canonicalTopologicalData.IsSquareIntegrable π)
    {κ : F.Carrierˣ →* ℂˣ} (hκ : IsNormTrivial E κ) :
    ∃ Q : ℂ[X], IsPadicRankLPolynomial F ψ ν.val π
      (twist (κ.comp determinant) (smoothContragredient π)) Q ∧
      Q.eval (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
  let T := F.canonicalTopologicalData
  let χ := κ.comp (determinant (n := n + 1))
  let σ := twist χ (smoothContragredient π)
  have hiπd := ((supercuspidalContragredient p F T (n + 1) V π hsπ.1.1).2 hsπ.1).mpr hiπ
  have his : σ.IsIrreducible := (isIrreducible_twist_iff χ _).mpr hiπd
  have hss : IsSupercuspidal σ := by
    let : NontriviallyNormedField F.Carrier := F.canonicalNormedField
    let : CompleteSpace F.Carrier := inferInstance
    let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    exact (hκ.isSupercuspidal_twist_iff _).mpr
      (isSupercuspidal_smoothContragredient F T (n + 1) V π hsπ)
  have hus : IsUnitarizable σ :=
    (isUnitarizable_twist_iff χ (fun g => hκ.norm_eq_one (determinant g)) _).mpr
      (isUnitarizable_of_squareIntegrable F _
        (T.isSquareIntegrable_smoothContragredient π hqπ) hiπd)
  have hw := isOfWhittakerType_of_isSupercuspidal F ψ n (SmoothRep.of σ hss.1.1) his hss
  obtain ⟨A, hA, hP⟩ := supercuspidalEqualRankLFactor p F ψ ν n π σ hiπ hsπ his hw
  refine ⟨_, (isPadicSymmetricLPolynomial_of_le le_rfl).mpr hP, ?_⟩
  rw [_root_.Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha heval
  have hun := IsContragredientTwistParameter.norm_eq_one F π σ ((hA a).mp ha)
    hiπ his hsπ.1 hss.1 (isUnitarizable_of_squareIntegrable F π hqπ hiπ) hus
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_zero] at heval
  have he := congrArg norm heval
  rw [norm_one, norm_mul, hun, one_mul, Complex.norm_natCast] at he
  exact (Nat.ne_of_gt T.residueCardinality_gt_one) (by exact_mod_cast he.symm)

/-- The certified lower denominator for `(π, κπ∨)`, with its nonvanishing at
the residue cardinality. -/
def normTwistedSupercuspidalSelfPairPolynomial
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hiπ : π.IsIrreducible) (hsπ : IsSupercuspidal π)
    (hqπ : F.canonicalTopologicalData.IsSquareIntegrable π)
    {κ : F.Carrierˣ →* ℂˣ} (hκ : IsNormTrivial E κ) :
    {Q : ℂ[X] // IsPadicRankLPolynomial F ψ ν.val π
      (twist (κ.comp determinant) (smoothContragredient π)) Q ∧
      Q.eval (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0} :=
  Classical.indefiniteDescription _
    (exists_normTwistedSupercuspidalSelfPairPolynomial F E ψ ν π hiπ hsπ hqπ hκ)

end Langlands.BaseChange
