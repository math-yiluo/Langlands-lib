import Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalysis
import Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationNonvanishing
/-!
# Auxiliary analysis for the two-block deformation

General facts used to prove that the deformed Whittaker functions are entire:
an entire function vanishing on an uncountable set vanishes; the same for finite
exponential sums `∑ b_i^u • w_i` with positive real bases in any complex vector space;
the integral `u ↦ ∫_K α β^u` over a compact set with `β` positive and locally constant
is entire. It also records that the inverse standard character has open kernel, that
the upper unipotent group has an increasing exhaustion by compact open subgroups, and
that the rectangular matrices have an exhaustion by compact sets.
-/

noncomputable section

open MeasureTheory Topology Filter

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding character_eq_one_mem_nhds exists_deformed_section_jacquetFunction_one_ne_zero exists_matrix_exhaustion exists_section_jacquetFunction_one_ne_zero exists_upperUnipotent_exhaustion isOpen_ker_inverseStandardCharacter isSmooth_twoBlockDeformedBlocks
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF

section Complex

end Complex

section Integral


end Integral

section Group

variable (F : Type uF) [Field F]

/-- The inverse standard character of the upper unipotent group has open kernel. -/
theorem isOpen_ker_inverseStandardCharacter [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) :
    IsOpen ((inverseStandardCharacter ψ n).ker : Set (upperUnipotent (n + 1) F)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (n + 1)
  let σ : upperUnipotent (n + 1) F → F := fun g =>
    ∑ k : Fin n, g.val k.castSucc k.succ
  have hc : Continuous σ :=
    continuous_finsetSum _ fun k _ => (UpperUnipotent.entry k.castSucc k.succ).continuous
  have h0 : σ 1 = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) k.castSucc k.succ = 0
    exact Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ)
  have hU : σ ⁻¹' {y : F | ψ.complex y = 1} ∈ 𝓝 (1 : upperUnipotent (n + 1) F) :=
    hc.continuousAt.preimage_mem_nhds (h0 ▸ character_eq_one_mem_nhds F ψ)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [hU] with g hg
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  rw [inverseStandardCharacter_apply]
  change (ψ.complex (σ g))⁻¹ = 1
  rw [show ψ.complex (σ g) = 1 from hg, inv_one]

/-- The upper unipotent group has an increasing exhaustion by compact open subgroups. -/
theorem exists_upperUnipotent_exhaustion [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    ∃ S : ℕ → OpenSubgroup (upperUnipotent n F),
      (∀ k, IsCompact (S k : Set (upperUnipotent n F))) ∧ Monotone S ∧
        ∀ g : upperUnipotent n F, ∃ k, g ∈ S k := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearSigmaCompactSpace n
  have : SigmaCompactSpace (upperUnipotent n F) :=
    (UpperUnipotent.isClosed (R := F) (n := n)).sigmaCompactSpace
  let U := upperUnipotent n F
  let Q := {K : OpenSubgroup U // IsCompact (K : Set U)}
  have step : ∀ C : Set U, IsCompact C → ∃ K : Q, C ⊆ (K.val : Set U) := by
    intro C hC
    obtain ⟨K, hK, hCK⟩ := upperUnipotentCompactContainment F T n C hC
    exact ⟨⟨K, hK⟩, hCK⟩
  let next : ℕ → Q → Q := fun j K =>
    (step _ ((isCompact_compactCovering U (j + 1)).union K.property)).choose
  let R : ℕ → Q := fun k => Nat.rec (step _ (isCompact_compactCovering U 0)).choose next k
  have hR0 : compactCovering U 0 ⊆ ((R 0).val : Set U) :=
    (step _ (isCompact_compactCovering U 0)).choose_spec
  have hRs : ∀ j, compactCovering U (j + 1) ∪ ((R j).val : Set U) ⊆ ((R (j + 1)).val : Set U) :=
    fun j => (step _ ((isCompact_compactCovering U (j + 1)).union (R j).property)).choose_spec
  have hcov : ∀ k, compactCovering U k ⊆ ((R k).val : Set U) := by
    intro k
    cases k with
    | zero => exact hR0
    | succ j => exact Set.subset_union_left.trans (hRs j)
  refine ⟨fun k => (R k).val, fun k => (R k).property, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun j => ?_
    intro g hg
    exact hRs j (Set.mem_union_right _ hg)
  · intro g
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ((iUnion_compactCovering U).symm ▸ Set.mem_univ g)
    exact ⟨k, hcov k hk⟩

/-- The rectangular matrices over `F` have a sequence of compact sets eventually containing
every compact set. -/
theorem exists_matrix_exhaustion [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ) :
    ∃ E : ℕ → Set (Matrix (Fin a) (Fin b) F), (∀ R, IsCompact (E R)) ∧
      ∀ C, IsCompact C → ∃ R, C ⊆ E R := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : SecondCountableTopology F := T.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin a) (Fin b) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → F))
  have : SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))
  let E := CompactExhaustion.choice (Matrix (Fin a) (Fin b) F)
  exact ⟨fun R => E R, E.isCompact, fun C hC => E.exists_superset_of_isCompact hC⟩

end Group

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
