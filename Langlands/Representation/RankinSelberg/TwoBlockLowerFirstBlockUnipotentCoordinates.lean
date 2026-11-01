import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasureTransport
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding

/-!
# Block coordinates of the prescribed lower-unipotent Haar

The prescribed Haar on `H⁻ = C⁻¹ N C` unfolds into the two diagonal unipotent
Haar measures and any supplied rectangular Haar, up to its integral-cube mass.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory GeneralLinear QuotientIntegration TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient
open scoped ENNReal

universe uF uR

section Rotation

variable {R : Type uR} [CommRing R] {n : ℕ} (C : BlockShape n)

/-- Block reversal conjugates a reversed-label Levi element onto the original one. -/
theorem reverseMatrix_mul_reverse_leviEmbedding (L : C.Levi R) (L' : C.reverse.Levi R)
    (hL : ∀ i, L' i = L i.rev) :
    C.reverseMatrix R * C.reverse.leviEmbedding R L' * (C.reverseMatrix R)⁻¹ =
      C.leviEmbedding R L := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := C.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := C.indexEquiv.surjective y
  obtain ⟨i, rfl⟩ := Fin.rev_surjective i
  obtain ⟨j, rfl⟩ := Fin.rev_surjective j
  change (MulAut.conj (C.reverseMatrix R) (C.reverse.leviEmbedding R L'))
      (C.index i.rev a) (C.index j.rev b) =
    C.leviEmbedding R L (C.index i.rev a) (C.index j.rev b)
  rw [C.reverseMatrix_conjugate_entry R]
  by_cases hij : i = j
  · subst j
    rw [C.reverse.leviEmbedding_apply_same R L' (i : Fin C.reverse.length) a b, hL i]
    exact (C.leviEmbedding_apply_same R L i.rev a b).symm
  · rw [C.reverse.leviEmbedding_apply_ne R _ a b hij,
      C.leviEmbedding_apply_ne R _ a b (fun h => hij (Fin.rev_injective h))]

end Rotation

section Algebra

open TwoBlockJacquet

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- `C⁻¹ diag'(n_0, n_1) C = diag(n_1, n_0)` for the reversed-shape block embedding. -/
theorem blockRotation_inv_mul_blockEmbedding_mul
    (n : TwoBlockUnipotentQuotient.BlockUnipotents (fun i => m i.rev) R) :
    (blockRotation h R)⁻¹ * TwoBlockUnipotentQuotient.blockEmbedding (reverse_sum h) R n *
        blockRotation h R =
      (succBlockShape m h).leviEmbedding R (blockPair (m := m) R ((n 1).val, (n 0).val)) := by
  rw [TwoBlockUnipotentQuotient.blockEmbedding_apply, blockRotation_inv]
  refine reverseMatrix_mul_reverse_leviEmbedding (succBlockShape m h) _ _ fun i => ?_
  fin_cases i
  · exact (blockPair_apply_one R ((n 1).val, (n 0).val)).symm
  · exact (blockPair_apply_zero R ((n 1).val, (n 0).val)).symm

/-- Conjugating reversed coordinates `diag'(n_0, n_1) u'(Z)` gives `diag(n_1, n_0) R(Z)`. -/
theorem blockRotation_inv_mul_coordinates_mul
    (n : TwoBlockUnipotentQuotient.BlockUnipotents (fun i => m i.rev) R)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    (blockRotation h R)⁻¹ * (TwoBlockUnipotentQuotient.blockEmbedding (reverse_sum h) R n *
        upperRadical (reverse_sum h) R Z) * blockRotation h R =
      (succBlockShape m h).leviEmbedding R (blockPair (m := m) R ((n 1).val, (n 0).val)) *
        lowerRadical h R Z := by
  rw [lowerRadical, ← blockRotation_inv_mul_blockEmbedding_mul h R n]
  group

end Algebra

section Measure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerUnipotentCoordinatesInstance01 : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance lowerUnipotentCoordinatesInstance02 : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance lowerUnipotentCoordinatesInstance03 : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance lowerUnipotentCoordinatesInstance04 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance lowerUnipotentCoordinatesInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerUnipotentCoordinatesInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerUnipotentCoordinatesInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance08 (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerUnipotentCoordinatesInstance09 (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerUnipotentCoordinatesInstance10 (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerUnipotentCoordinatesInstance11 (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerUnipotentCoordinatesInstance12 (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance13 (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerUnipotentCoordinatesInstance14 (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerUnipotentCoordinatesInstance15 (n : ℕ) :
    MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerUnipotentCoordinatesInstance16 (n : ℕ) :
    BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance17 (n : ℕ) :
    SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerUnipotentCoordinatesInstance18 (n : ℕ) :
    LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerUnipotentCoordinatesInstance19 :
    MeasurableSpace (lowerBlockUnipotent h F.Carrier) := borel _
local instance lowerUnipotentCoordinatesInstance20 :
    BorelSpace (lowerBlockUnipotent h F.Carrier) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance21 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h' F.Carrier) := borel _
local instance lowerUnipotentCoordinatesInstance22 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h' F.Carrier) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance23 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    SecondCountableTopology (TwoBlockUnipotentQuotient.blockUnipotent h' F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

local notation "O" => Valuation.integer (ValuativeRel.valuation F.Carrier)

local instance lowerUnipotentCoordinatesInstance24 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    LocallyCompactSpace (TwoBlockUnipotentQuotient.blockUnipotent h' F.Carrier) :=
  (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h' F.Carrier).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The prescribed lower-unipotent Haar is the inverse-conjugation transport of the
standard full-unipotent Haar. -/
theorem lintegral_lowerHaar_eq (ψ : GeneralLinear (t + 1) F.Carrier → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ x : lowerBlockUnipotent h F.Carrier, ψ x.val ∂lowerHaar F h =
      ∫⁻ n : upperUnipotent (t + 1) F.Carrier,
        ψ ((blockRotation h F.Carrier)⁻¹ * n.val * blockRotation h F.Carrier)
          ∂unipotentHaar F.Carrier t := by
  rw [lowerHaar]
  exact lintegral_map (hψ.comp continuous_subtype_val.measurable)
    (continuous_conjugationEquiv_symm_canonical F h).measurable

/-- The block coordinates `(b, Z) ↦ b u(Z)` of the standard full-unipotent Haar, for any
two-block shape, with the fixed block measure unfolded into the two block Haar measures. -/
theorem lintegral_unipotentHaar_blockCoordinates {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t + 1)
    (μR : Measure (Matrix (Fin (m' 0 + 1)) (Fin (m' 1 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
    (φ : upperUnipotent (t + 1) F.Carrier → ℝ≥0∞) (hφ : Measurable φ) :
    μR {Z | ∀ i j, Z i j ∈ O} * ∫⁻ n, φ n ∂unipotentHaar F.Carrier t =
      ∫⁻ y : upperUnipotent (m' 0 + 1) F.Carrier, ∫⁻ x : upperUnipotent (m' 1 + 1) F.Carrier,
        ∫⁻ Z, φ (TwoBlockUnipotentQuotientIntegration.coordinates h'
          (TwoBlockUnipotentQuotient.blockUnipotentEquiv h' F.Carrier
            ((MeasurableEquiv.piFinTwo _).symm (y, x)), Z)) ∂μR
          ∂unipotentHaar F.Carrier (m' 1) ∂unipotentHaar F.Carrier (m' 0) := by
  have hcoord := TwoBlockUnipotentQuotientIntegration.map_coordinates_prod F.Carrier h'
    (TwoBlockUnipotentQuotient.blockHaar F.Carrier h')
    (TwoBlockUnipotentQuotientIntegration.blockMeasure_integral F.Carrier h') μR
  have hcm : Measurable (TwoBlockUnipotentQuotientIntegration.coordinates (K := F.Carrier) h') :=
    (TwoBlockUnipotentQuotientIntegration.continuous_coordinates h').measurable
  have hprod := hφ.comp hcm
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← hcoord, lintegral_map hφ hcm]
  refine (lintegral_prod _ hprod.aemeasurable).trans ?_
  exact lintegral_blockHaar F h' _ hprod.lintegral_prod_right'

/-- **Block coordinates of `H⁻`.** For every rectangular additive Haar `μR`,
the integral-cube mass of `μR` times the prescribed lower-unipotent Haar integral
equals the iterated integral over `diag(x, y) R(Z)` with `x ∈ N_a`, `y ∈ N_b`. -/
theorem lintegral_lowerHaar
    (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
    (ψ : GeneralLinear (t + 1) F.Carrier → ℝ≥0∞) (hψ : Measurable ψ) :
    μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ x : lowerBlockUnipotent h F.Carrier, ψ x.val ∂lowerHaar F h =
      ∫⁻ y : upperUnipotent (m 1 + 1) F.Carrier, ∫⁻ x : upperUnipotent (m 0 + 1) F.Carrier,
        ∫⁻ Z, ψ ((succBlockShape m h).leviEmbedding F.Carrier
            (blockPair (m := m) F.Carrier (x.val, y.val)) * lowerRadical h F.Carrier Z)
          ∂μR ∂unipotentHaar F.Carrier (m 0) ∂unipotentHaar F.Carrier (m 1) := by
  have hφ : Measurable (fun n : upperUnipotent (t + 1) F.Carrier =>
      ψ ((blockRotation h F.Carrier)⁻¹ * n.val * blockRotation h F.Carrier)) :=
    hψ.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  rw [lintegral_lowerHaar_eq F h ψ hψ]
  refine (lintegral_unipotentHaar_blockCoordinates F (m' := fun i => m i.rev) (reverse_sum h)
    μR _ hφ).trans ?_
  refine lintegral_congr fun y => lintegral_congr fun x => lintegral_congr fun Z => ?_
  rw [TwoBlockUnipotentQuotientIntegration.coordinates_val,
    TwoBlockUnipotentQuotient.blockUnipotentEquiv_apply_val,
    blockRotation_inv_mul_coordinates_mul h F.Carrier]
  rfl

end Measure

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
