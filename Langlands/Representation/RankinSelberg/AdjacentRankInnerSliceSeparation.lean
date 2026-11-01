import Langlands.Representation.RankinSelberg.AdjacentRankDeterminantShells
import Langlands.Representation.RankinSelberg.AdjacentRankCompactCoefficients
import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.Representation.GodementJacquet.WhittakerAveraging
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Representation.MatrixCoefficient.LawsProof

/-! The inner determinant-slice separation of JPSS Section 6.3, (6)--(9). -/

noncomputable section

namespace Langlands.GodementJacquet

universe uG uV

/-- The entire bi-smooth coefficient span consists of locally constant functions. -/
theorem isLocallyConstant_biSmoothMatrixCoefficients
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (f : biSmoothMatrixCoefficients σ) :
    IsLocallyConstant f.val := by
  have h : ∀ f ∈ biSmoothMatrixCoefficients σ, IsLocallyConstant f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨L, v, rfl⟩ := hx
      exact matrixCoefficient_isLocallyConstant σ _ _ v.property
    | zero => exact IsLocallyConstant.const 0
    | add x y _ _ hx hy => exact hx.comp₂ hy (· + ·)
    | smul c x _ hx => exact hx.comp (c • ·)
  exact h f.val f.property

end Langlands.GodementJacquet

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker
open scoped BigOperators Topology

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance (r : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance (r : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)

/-- A single compact open subgroup, stable under inverse transpose, fixes the
square test and is trivial under both determinant characters. -/
theorem exists_adjacentRankInner_subgroup {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) :
    ∃ K : OpenSubgroup (Langlands.GeneralLinear (r + 1) F.Carrier),
      IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) ∧
      (∀ k ∈ K, GeneralLinear.inverseTranspose (r + 1) F.Carrier k ∈ K) ∧
      ∀ k ∈ K,
        (∀ M, Φ (k.val * M) = Φ M) ∧
        χ (GeneralLinear.determinant k) = 1 ∧
        F.canonicalTopologicalData.normalizedAbs (Matrix.det k.val) = 1 := by
  let T := F.canonicalTopologicalData
  let G := Langlands.GeneralLinear (r + 1) F.Carrier
  let := T.generalLinearNonarchimedean (r + 1)
  let θ : G →* ℂˣ := (χ : F.Carrierˣ →* ℂˣ).comp GeneralLinear.determinant
  have hθ : IsOpen (θ.ker : Set G) :=
    isOpen_ker_of_continuous_complex_character θ
      (χ.continuous.comp (T.generalLinearDeterminant (r + 1)).continuous)
  obtain ⟨U, hUc, hU⟩ :=
    GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  let C : OpenSubgroup G := ⟨θ.ker, hθ⟩
  let L := U ⊓ C
  let Li := L.comap (GeneralLinear.inverseTranspose (r + 1) F.Carrier).toMonoidHom
    (GeneralLinear.continuous_inverseTranspose (r + 1) F.Carrier)
  let K := L ⊓ Li
  have hLc : IsCompact (L : Set G) := hUc.inter_right C.isClosed
  refine ⟨K, hLc.inter_right Li.isClosed, ?_, ?_⟩
  · intro k hk
    exact ⟨hk.2, by
      change GeneralLinear.inverseTranspose (r + 1) F.Carrier
        (GeneralLinear.inverseTranspose (r + 1) F.Carrier k) ∈ L
      rw [GeneralLinear.inverseTranspose_involutive]
      exact hk.1⟩
  · intro k hk
    exact ⟨(hU k hk.1.1).1, hk.1.2, (hU k hk.1.1).2⟩

/-- The actual compactly supported weight in the inner determinant-slice
integral, for every order and every complex exponent. -/
def adjacentRankInnerSliceWeight {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) (j : ℤ) (s : ℂ)
    (h : Langlands.GeneralLinear (r + 1) F.Carrier) : ℂ :=
  matrixSliceTest F.canonicalTopologicalData r Φ j h *
    (χ (GeneralLinear.determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h s

theorem continuous_adjacentRankInnerSliceWeight {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) (j : ℤ) (s : ℂ) :
    Continuous (adjacentRankInnerSliceWeight F Φ χ j s) := by
  exact (((matrixSliceTest F.canonicalTopologicalData r Φ j).continuous.mul
    (Units.continuous_val.comp (χ.continuous.comp
      (F.canonicalTopologicalData.generalLinearDeterminant (r + 1)).continuous))).mul
    (continuous_adjacentRank_determinantWeight F (r + 1) s))

theorem hasCompactSupport_adjacentRankInnerSliceWeight {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) (j : ℤ) (s : ℂ) :
    HasCompactSupport (adjacentRankInnerSliceWeight F Φ χ j s) :=
  (matrixSliceTest F.canonicalTopologicalData r Φ j).hasCompactSupport.mul_right.mul_right

/-- Slice integrability holds for every continuous coefficient, with no growth
or right-half-plane premise. -/
theorem integrable_adjacentRankInnerSliceWeight_mul {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) (j : ℤ) (s : ℂ)
    (f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (hf : Continuous f) :
    Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * f h)
      (generalLinearHaar F.Carrier r) :=
  ((continuous_adjacentRankInnerSliceWeight F Φ χ j s).mul hf).integrable_of_hasCompactSupport
    (hasCompactSupport_adjacentRankInnerSliceWeight F Φ χ j s).mul_right

/-- The character and test conditions on the averaging subgroup make the
complete slice weight left invariant. -/
theorem adjacentRankInnerSliceWeight_mul {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier)
    (k : Langlands.GeneralLinear (r + 1) F.Carrier)
    (hΦ : ∀ M, Φ (k.val * M) = Φ M)
    (hχ : χ (GeneralLinear.determinant k) = 1)
    (hdet : F.canonicalTopologicalData.normalizedAbs (Matrix.det k.val) = 1)
    (j : ℤ) (s : ℂ) (h : Langlands.GeneralLinear (r + 1) F.Carrier) :
    adjacentRankInnerSliceWeight F Φ χ j s (k * h) =
      adjacentRankInnerSliceWeight F Φ χ j s h := by
  let T := F.canonicalTopologicalData
  have hord : T.ord (GeneralLinear.determinant k : F.Carrier) = 0 :=
    (T.ord_eq_zero_iff_normalizedAbs (GeneralLinear.determinant k)).mpr hdet
  have hs : k * h ∈ generalLinearDeterminantSlice T r j ↔
      h ∈ generalLinearDeterminantSlice T r j := by
    simp only [mem_generalLinearDeterminantSlice, map_mul, Units.val_mul]
    rw [T.ord_mul (GeneralLinear.determinant k).ne_zero
      (GeneralLinear.determinant h).ne_zero, hord, zero_add]
  have hw : determinantWeight (normalizedAbsoluteValue T) (k * h) s =
      determinantWeight (normalizedAbsoluteValue T) h s := by
    simp only [determinantWeight, Units.val_mul, Matrix.det_mul, AbsoluteValue.map_mul]
    rw [show normalizedAbsoluteValue T (Matrix.det k.val) = 1 from hdet, one_mul]
  by_cases hh : h ∈ generalLinearDeterminantSlice T r j
  · have hkh := hs.mpr hh
    dsimp only [T] at hh hkh hw
    simp only [adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_mem hh, Set.indicator_of_mem hkh, Units.val_mul, hΦ,
      map_mul, hχ, one_mul, hw]
  · have hkh : k * h ∉ generalLinearDeterminantSlice T r j := fun he => hh (hs.mp he)
    dsimp only [T] at hh hkh
    simp only [adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_notMem hh, Set.indicator_of_notMem hkh, zero_mul]

set_option maxHeartbeats 1000000 in
/-- Finite separation of each genuinely convergent inner slice integral.
The subgroup, basis and coefficients are chosen before the slice, exponent
and external group element. -/
theorem adjacentRankInnerSlice_finiteSeparation
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier) :
    ∃ (N : ℕ) (B : Fin N → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          ∀ (j : ℤ) (s : ℂ) (g : Langlands.GeneralLinear (r + 1) F.Carrier),
            Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h *
              glModelFunction ψ r σ ℓ W (g * h)) (generalLinearHaar F.Carrier r) ∧
            (∀ i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h)
              (generalLinearHaar F.Carrier r)) ∧
            (∫ h, adjacentRankInnerSliceWeight F Φ χ j s h *
                glModelFunction ψ r σ ℓ W (g * h) ∂generalLinearHaar F.Carrier r) =
              ∑ i, glModelFunction ψ r σ ℓ (B i) g *
                ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h
                  ∂generalLinearHaar F.Carrier r := by
  obtain ⟨K, hKc, -, hK⟩ := exists_adjacentRankInner_subgroup F Φ χ
  obtain ⟨N, B, hB⟩ := adjacentRankCompact_middleAverage F ψ σ hσ ℓ K hKc
  refine ⟨N, B, fun W => ?_⟩
  obtain ⟨f, hf⟩ := hB W
  refine ⟨f, fun j s g => ?_⟩
  let μ := generalLinearHaar F.Carrier r
  let a := adjacentRankInnerSliceWeight F Φ χ j s
  let mass : ℂ := μ.real (K : Set _)
  have hmass : mass ≠ 0 :=
    GodementJacquet.Padic.measureReal_openSubgroup_ne_zero F K hKc
  have hW : Integrable (fun h => a h * glModelFunction ψ r σ ℓ W (g * h)) μ :=
    integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s _
      ((glModelFunction_continuous ψ r σ hσ.1 ℓ W).comp (continuous_const.mul continuous_id))
  have hfi (i : Fin N) : Integrable (fun h => a h * (f i).val h) μ :=
    integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s _
      (GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients _ (f i)).continuous
  have ha : ∀ k ∈ K, ∀ h, a (k * h) = a h := by
    intro k hk h
    obtain ⟨hΦk, hχk, hdet⟩ := hK k hk
    exact adjacentRankInnerSliceWeight_mul F Φ χ k hΦk hχk hdet j s h
  obtain ⟨-, hval⟩ := GodementJacquet.leftAverage_integral μ (K : Set _)
    K.isOpen.measurableSet hKc.measure_lt_top.ne a
    (fun h => glModelFunction ψ r σ ℓ W (g * h)) ha hW
  have hnorm :
      (∫ h, a h * (mass⁻¹ * ∫ k in (K : Set _),
        glModelFunction ψ r σ ℓ W (g * (k * h)) ∂μ) ∂μ) =
        ∫ h, a h * glModelFunction ψ r σ ℓ W (g * h) ∂μ := by
    calc
      _ = mass⁻¹ * ∫ h, a h * (∫ k in (K : Set _),
          glModelFunction ψ r σ ℓ W (g * (k * h)) ∂μ) ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext h
        ring
      _ = _ := by rw [hval, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]
  refine ⟨hW, hfi, ?_⟩
  calc
    _ = ∫ h, a h * (mass⁻¹ * ∫ k in (K : Set _),
        glModelFunction ψ r σ ℓ W (g * (k * h)) ∂μ) ∂μ := hnorm.symm
    _ = ∫ h, ∑ i, glModelFunction ψ r σ ℓ (B i) g * (a h * (f i).val h) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun h => by
        dsimp only
        have hsep : mass⁻¹ * (∫ k in (K : Set _),
            glModelFunction ψ r σ ℓ W (g * (k * h)) ∂μ) =
              ∑ i, glModelFunction ψ r σ ℓ (B i) g * (f i).val h := by
          simpa only [mass, μ, mul_assoc] using hf g h
        rw [hsep, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, glModelFunction ψ r σ ℓ (B i) g * ∫ h, a h * (f i).val h ∂μ := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hfi i).const_mul _)]
      simp only [integral_const_mul]

end Langlands.RankinSelberg.Padic
