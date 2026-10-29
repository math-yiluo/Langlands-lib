import Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.Induction.OppositeProductReversalProof

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

namespace Langlands.RankinSelberg.TwoBlockDeformation

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private theorem isTopologicalRing :
    letI := F.canonicalTopologicalData.topology
    IsTopologicalRing F.Carrier := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance

/-- A deformed block has full Whittaker type for a character exactly when the
original block does: the twist `|det|^u` has open kernel and is trivial on the
upper unipotent subgroup. -/
theorem twoBlockDeformedBlocks_isOfWhittakerType_iff
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ)
    (i : Fin 2) (θ : upperUnipotent (m i + 1) F.Carrier →* ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType (m i) θ (twoBlockDeformedBlocks F m σ u i) ↔
      IsOfWhittakerType (m i) θ (σ i) :=
  letI := F.canonicalTopologicalData.topology
  isOfWhittakerType_twist_iff θ _ (σ i)
    (F.canonicalTopologicalData.isOpen_ker_determinantComplexPower (m i + 1) _)
    (determinantComplexPower_upperUnipotent F (m i + 1) _)

/-- Every block of full standard Whittaker type has a nonzero inverse-character
functional. -/
theorem exists_block_inverse_functional
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (i : Fin 2) :
    letI := F.canonicalTopologicalData.topology
    ∃ l : glInverseFunctionals ψ (m i) (σ i), l.val ≠ 0 := by
  let := F.canonicalTopologicalData.topology
  let := isTopologicalRing F
  exact ((isOfWhittakerType_standard_iff_inverse ψ (σ i)).1 (hσ i)).exists_ne_zero

/-- An inverse-character functional of the block `σ i` is, with the same linear map,
an inverse-character functional of the deformed block at every `u`, because
`|det|^u` is trivial on the upper unipotent subgroup. -/
def deformedBlockFunctional
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ)
    (i : Fin 2) (l : letI := F.canonicalTopologicalData.topology;
      glInverseFunctionals ψ (m i) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    glInverseFunctionals ψ (m i) (twoBlockDeformedBlocks F m σ u i) :=
  letI := F.canonicalTopologicalData.topology
  twistFunctional (upperUnipotent (m i + 1) F.Carrier) (inverseStandardCharacter ψ (m i))
    (F.canonicalTopologicalData.determinantComplexPower (m i + 1) (if i = 0 then u else 0))
    (determinantComplexPower_upperUnipotent F (m i + 1) _) (σ i) l

@[simp]
theorem deformedBlockFunctional_val
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ)
    (i : Fin 2) (l : letI := F.canonicalTopologicalData.topology;
      glInverseFunctionals ψ (m i) (σ i)) :
    (deformedBlockFunctional F m ψ σ u i l).val = l.val :=
  rfl

/-- Conditional on `NormalizedProductWhittakerTypeStatement`, the deformed lower
induction `ρ_u` has full inverse-standard Whittaker type for every complex `u`. It is
equivalent to the upper normalized induction of the reversed deformed blocks. -/
theorem isOfWhittakerType_twoBlockDeformedInduced
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType t (inverseStandardCharacter ψ t) (twoBlockDeformedInduced F m h σ u) := by
  let := F.canonicalTopologicalData.topology
  let := isTopologicalRing F
  have hu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (twoBlockDeformedBlocks F m σ u i) := fun i =>
    (twoBlockDeformedBlocks_isOfWhittakerType_iff F m σ u i _).2 (hσ i)
  have hs : ∀ i, IsSmooth (twoBlockDeformedBlocks F m σ u i) := fun i => (hu i).1.1
  obtain ⟨E, -, -⟩ := glOppositeProductReversal p F F.canonicalTopologicalData (t + 1)
    (succBlockShape m h) W (twoBlockDeformedBlocks F m σ u) hs
  have h' : ∑ i : Fin 2, (m i.rev + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  have hup := H p F ψ t 2 (fun i => m i.rev) h' (W := fun i => W i.rev)
    (fun i => twoBlockDeformedBlocks F m σ u i.rev) (fun i => hu i.rev)
  exact (isOfWhittakerType_standard_iff_inverse ψ _).1 (hup.of_equiv E.symm)

/-- Conditional on `NormalizedProductWhittakerTypeStatement`, every inverse-character
functional on `ρ_u` is a multiple of any nonzero one. -/
theorem functional_eq_smul
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ)
    (ℓ ℓ' : letI := F.canonicalTopologicalData.topology;
      glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u))
    (hℓ : ℓ.val ≠ 0) :
    ∃ c : ℂ, ℓ'.val = c • ℓ.val := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨c, hc⟩ :=
    (isOfWhittakerType_twoBlockDeformedInduced F m h H ψ σ hσ u).eq_smul hℓ ℓ'
  exact ⟨c, congrArg Subtype.val hc⟩

end Langlands.RankinSelberg.TwoBlockDeformation
