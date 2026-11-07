import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.Factors.HeckeFunctionalEquationStatement
import Langlands.LocalFactor.Harmonic.NormalizationProof

/-! # The unramified finite epsilon factor at conductor zero -/

noncomputable section

open MeasureTheory

namespace Langlands.Global.HeckeFunctionalEquation

universe u

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- Every supplied self-dual Haar measure gives the integers volume one when
the actual additive conductor is zero. -/
theorem selfDualHaar_integerRing_eq_one (ψ : AdditiveCharacter)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
    (hn : T.additiveConductor ψ = 0) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel _
    μ.val.measure (LocalFactor.PadicAbelian.integerRing T) = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have hc : IsGreatest {m : ℤ | ∀ t : T.Integers,
      ψ (T.uniformizer ^ (-m) * (t : F.Carrier)) = 1} 0 := by
    simpa only [hn] using T.isGreatest_fractionalIdeal_triviality ψ
  have hnorm := (LocalFactors.padicFourierNormalization p F T ψ.toAddChar
    ψ.continuous_toFun ψ.nontrivial 0 hc).2.1 μ.val.measure μ.val.isAddHaar
  have hmass := hnorm.mp (by
    intro f hlc hcomp x
    have h := (μ.property ⟨f, hlc, hcomp⟩).2 x
    change (∫ z, ψ.complex (z * x) *
      (∫ w, ψ.complex (w * z) * f w ∂μ.val.measure) ∂μ.val.measure) = f (-x) at h
    simpa only [Fourier.fourierIntegral_def, AddChar.inv_apply, neg_neg,
      Circle.smul_def, smul_eq_mul,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply] using h)
  simpa [LocalFactor.PadicAbelian.integerRing] using hmass

/-- At zero multiplicative and additive conductor, the exact fixed-Haar
epsilon expression is one at every complex spectral parameter. -/
theorem epsilon_eq_one_of_conductors_eq_zero (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
    (ha : T.multiplicativeConductor χ = 0) (hn : T.additiveConductor ψ = 0)
    (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel _
    LocalFactor.PadicAbelian.epsilon T χ ψ μ.val.measure s = 1 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel _
  have hμ := selfDualHaar_integerRing_eq_one T ψ μ hn
  simp [LocalFactor.PadicAbelian.epsilon, LocalFactor.PadicAbelian.epsilonAt,
    ha, hn, hμ]

end Local

section Global

open NumberField

variable {K : Type u} [Field K] [NumberField K]

/-- The integer ring used by the local conductor is the completed integer ring
at the actual finite place. -/
theorem mem_localIntegers_iff (v : FinitePlace K) (x : FiniteCompletion K v) :
    x ∈ (CompletionPadic.topologicalData v).Integers ↔
      x ∈ v.adicCompletionIntegers K := by
  let := (CompletionPadic.topologicalData v).valuativeRel
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  change ValuativeRel.valuation (FiniteCompletion K v) x ≤ 1 ↔ _
  rw [← (ValuativeRel.valuation (FiniteCompletion K v)).vle_one_iff]
  simpa only [map_one] using CompletionPadic.topologicalData_vle v x 1

/-- Unramifiedness of the actual Hecke character gives zero for the intrinsic
local multiplicative conductor. -/
theorem multiplicativeConductor_eq_zero_of_isUnramifiedAt
    (χ : HeckeCharacter K) (v : FinitePlace K) (hχ : χ.IsUnramifiedAt v) :
    (CompletionPadic.topologicalData v).multiplicativeConductor
      (χ.finiteComponent v) = 0 := by
  apply ((CompletionPadic.topologicalData v).multiplicativeConductor_eq_zero_iff
    (χ.finiteComponent v)).mpr
  intro x hx
  apply hχ x
  constructor
  · apply (mem_localIntegers_iff v _).mp
    exact ((CompletionPadic.topologicalData v).mem_integers_iff_discreteValuation_le_one
      (x : FiniteCompletion K v)).mpr hx.le
  · apply (mem_localIntegers_iff v _).mp
    apply ((CompletionPadic.topologicalData v).mem_integers_iff_discreteValuation_le_one
      (↑x⁻¹ : FiniteCompletion K v)).mpr
    simpa only [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one] using
      (le_refl (1 : WithZero (Multiplicative ℤ)))

/-- The finite epsilon expression appearing verbatim in the global target,
at the supplied local characters and supplied self-dual Haar measures. -/
def finiteEpsilon (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (v : FinitePlace K) (s : ℂ) : ℂ :=
  letI := (CompletionPadic.topologicalData v).topology
  letI : MeasurableSpace (CompletionPadic.padicField v).Carrier := borel _
  LocalFactor.PadicAbelian.epsilon (CompletionPadic.topologicalData v) (χ.finiteComponent v)
    (ψf v) (μ v).val.measure s

/-- Outside an explicit finite additive exceptional set and a finite
multiplicative ramification set, the exact finite epsilon is one. -/
theorem exists_finset_finiteEpsilon_eq_one_of_additiveConductor
    (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (Sψ : Finset (FinitePlace K))
    (hψ : ∀ v ∉ Sψ, (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ s : ℂ, finiteEpsilon χ ψf μ v s = 1 := by
  classical
  obtain ⟨Sχ, hχ⟩ := exists_finset_isUnramifiedAt K χ
  refine ⟨Sχ ∪ Sψ, fun v hv s => ?_⟩
  have hvχ : v ∉ Sχ := fun h => hv (Finset.mem_union_left _ h)
  have hvψ : v ∉ Sψ := fun h => hv (Finset.mem_union_right _ h)
  exact epsilon_eq_one_of_conductors_eq_zero (CompletionPadic.topologicalData v)
    (χ.finiteComponent v) (ψf v) (μ v)
    (multiplicativeConductor_eq_zero_of_isUnramifiedAt χ v (hχ v hvχ)) (hψ v hvψ) s

end Global

end Langlands.Global.HeckeFunctionalEquation
