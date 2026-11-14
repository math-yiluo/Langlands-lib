import Langlands.Representation.RankinSelberg.TwoBlockDeformationUniqueness
import Langlands.AllField.Representation.Induction.OppositeProductReversalProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement
/-!
# Uniqueness of inverse-character functionals on the deformed induction

Conditional on `NormalizedProductWhittakerTypeStatement` (normalized upper block
induction preserves full standard Whittaker type), the deformed lower induction
`ρ_u = Ind(G_t, Q̄; σ_1 ⊗ α^u, σ_2)` has full inverse-standard Whittaker type for
every complex `u`. Hence any two inverse-character functionals on `ρ_u` are
proportional when the first is nonzero. Each block of full standard type also has
a nonzero inverse-character functional.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding deformedBlockFunctional deformedBlockFunctional_val exists_block_inverse_functional functional_eq_smul isOfWhittakerType_twoBlockDeformedInduced twoBlockDeformedBlocks_isOfWhittakerType_iff
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uW

variable (F : Type uF) [Field F]
variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private theorem isTopologicalRing [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsTopologicalRing F := by
  infer_instance

/-- A deformed block has full Whittaker type for a character exactly when the
original block does: the twist `|det|^u` has open kernel and is trivial on the
upper unipotent subgroup. -/
theorem twoBlockDeformedBlocks_isOfWhittakerType_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)) (u : ℂ)
    (i : Fin 2) (θ : upperUnipotent (m i + 1) F →* ℂˣ) :
    IsOfWhittakerType (m i) θ (twoBlockDeformedBlocks F m σ u i) ↔
      IsOfWhittakerType (m i) θ (σ i) :=
  isOfWhittakerType_twist_iff θ _ (σ i)
    ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantComplexPower (m i + 1) _)
    (determinantComplexPower_upperUnipotent F (m i + 1) _)

/-- Every block of full standard Whittaker type has a nonzero inverse-character
functional. -/
theorem exists_block_inverse_functional [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (i : Fin 2) :
    ∃ l : glInverseFunctionals ψ (m i) (σ i), l.val ≠ 0 := by
  let := isTopologicalRing F
  exact ((isOfWhittakerType_standard_iff_inverse ψ (σ i)).1 (hσ i)).exists_ne_zero

/-- An inverse-character functional of the block `σ i` is, with the same linear map,
an inverse-character functional of the deformed block at every `u`, because
`|det|^u` is trivial on the upper unipotent subgroup. -/
def deformedBlockFunctional [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)) (u : ℂ)
    (i : Fin 2) (l : glInverseFunctionals ψ (m i) (σ i)) :
    glInverseFunctionals ψ (m i) (twoBlockDeformedBlocks F m σ u i) :=
  twistFunctional (upperUnipotent (m i + 1) F) (inverseStandardCharacter ψ (m i))
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1) (if i = 0 then u else 0))
    (determinantComplexPower_upperUnipotent F (m i + 1) _) (σ i) l

@[simp]
theorem deformedBlockFunctional_val [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)) (u : ℂ)
    (i : Fin 2) (l : glInverseFunctionals ψ (m i) (σ i)) :
    (deformedBlockFunctional F m ψ σ u i l).val = l.val :=
  rfl

/-- Conditional on `NormalizedProductWhittakerTypeStatement`, the deformed lower
induction `ρ_u` has full inverse-standard Whittaker type for every complex `u`. It is
equivalent to the upper normalized induction of the reversed deformed blocks. -/
theorem isOfWhittakerType_twoBlockDeformedInduced [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ) :
    IsOfWhittakerType t (inverseStandardCharacter ψ t) (twoBlockDeformedInduced F m h σ u) := by
  let := isTopologicalRing F
  have hu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (twoBlockDeformedBlocks F m σ u i) := fun i =>
    (twoBlockDeformedBlocks_isOfWhittakerType_iff F m σ u i _).2 (hσ i)
  have hs : ∀ i, IsSmooth (twoBlockDeformedBlocks F m σ u i) := fun i => (hu i).1.1
  obtain ⟨E, -, -⟩ := glOppositeProductReversal F (⟨⟩ : LocalFieldData F) (t + 1)
    (succBlockShape m h) W (twoBlockDeformedBlocks F m σ u) hs
  have h' : ∑ i : Fin 2, (m i.rev + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  have hup := H F ψ t 2 (fun i => m i.rev) h' (W := fun i => W i.rev)
    (fun i => twoBlockDeformedBlocks F m σ u i.rev) (fun i => hu i.rev)
  exact (isOfWhittakerType_standard_iff_inverse ψ _).1 (hup.of_equiv E.symm)

/-- Conditional on `NormalizedProductWhittakerTypeStatement`, every inverse-character
functional on `ρ_u` is a multiple of any nonzero one. -/
theorem functional_eq_smul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ)
    (ℓ ℓ' : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u))
    (hℓ : ℓ.val ≠ 0) :
    ∃ c : ℂ, ℓ'.val = c • ℓ.val := by
  obtain ⟨c, hc⟩ :=
    (isOfWhittakerType_twoBlockDeformedInduced F m h H ψ σ hσ u).eq_smul hℓ ℓ'
  exact ⟨c, congrArg Subtype.val hc⟩

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
