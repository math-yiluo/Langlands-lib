import Langlands.BushnellKutzko.SimpleCharacterTransferRelative
import Langlands.BushnellKutzko.PureStratumApproximationMaximalReduction

/-! # A common critical approximation on two normalized chains -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

open PureApproximation

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- A simple approximation on the generated-field line lifts to both chains through
one relative splitting basis. The two critical depths have a common normalized value. -/
theorem exists_common_critical_approximation
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (L M : LatticeChain 𝒪[F] F V) (n₁ n₂ : ℤ) (β : A) (r₁ : ℤ)
    (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hvL : L.valuation β = ((-n₁ : ℤ) : WithTop ℤ))
    (hvM : M.valuation β = ((-n₂ : ℤ) : WithTop ℤ))
    (hkL : criticalExponent L β = ((-r₁ : ℤ) : WithBot ℤ)) (hr₁ : r₁ < n₁) :
    ∃ (U W : Stratum 𝒪[F] F V) (r₀ : ℤ),
      U.chain = L ∧ W.chain = M ∧ U.n = n₁ ∧ W.n = n₂ ∧ U.r = r₁ ∧ U.b = W.b ∧
      U.IsSimple ∧ W.IsSimple ∧
      criticalExponent L β = ((-U.r : ℤ) : WithBot ℤ) ∧
      criticalExponent M β = ((-W.r : ℤ) : WithBot ℤ) ∧
      U.b - β ∈ L.endFiltration (-U.r) ∧ W.b - β ∈ M.endFiltration (-W.r) ∧
      U.r = ((L.period / elementRamificationIndex F β : ℕ) : ℤ) * r₀ ∧
      W.r = ((M.period / elementRamificationIndex F β : ℕ) : ℤ) * r₀ ∧
      elementRamificationIndex F U.b ∣ elementRamificationIndex F β := by
  classical
  let E : Type uV := elementAlgebra β
  let : Field E := hf.toField
  let := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β))
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isFractionRing F E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let bE : E := elementGenerator β
  let b : Module.End F E := subfieldEmbedding F E E bE
  have hbGen : Algebra.adjoin F ({bE} : Set E) = ⊤ := adjoin_elementGenerator β
  have hbEmb : subfieldEmbedding F E V bE = β := subfieldEmbedding_elementGenerator β hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  let hInt := isIntegral_iff_mem_spectralInteger F E
  let L' := L.relativeLatticeChain hL hInt
  let M' := M.relativeLatticeChain hM hInt
  obtain ⟨q, w, hwN, hwL', hwM'⟩ := L'.exists_common_splitting_basis M' hρ
  obtain ⟨j⟩ := hwN
  have hwL : RelSplits (L := E) L w := fun i c hc => hwL' c i hc
  have hwM : RelSplits (L := E) M w := fun i c hc => hwM' c i hc
  let C : LatticeChain 𝒪[F] F E := subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  have hC : ∀ u : Eˣ, subfieldUnits F E E u ∈ C.stabilizer :=
    subfieldBasisChain_normalized (Module.Basis.singleton Unit E) hϖ
  have hbN : NormalizingUnits C (elementAlgebra b) := by
    have heq : elementAlgebra b = (subfieldEmbedding F E E).range := by
      change Algebra.adjoin F ({subfieldEmbedding F E E bE} : Set (Module.End F E)) = _
      rw [← AlgHom.map_adjoin_singleton (subfieldEmbedding F E E) bE, hbGen, Algebra.map_top]
    rw [heq]
    intro x hx hx0
    obtain ⟨a, rfl⟩ := hx
    have ha : a ≠ 0 := fun ha => hx0 (by simp [ha])
    exact ⟨subfieldUnits F E E (Units.mk0 a ha), rfl, hC _⟩
  have hb : diagonal F w b = β := by
    change diagonal F w (LinearMap.mulLeft F bE) = β
    rw [diagonal_mulLeft, hbEmb]
  have hb0 : b ≠ 0 := by
    intro h
    have hz : β = 0 := by rw [← hb, h, map_zero]
    rw [hz, L.valuation_zero] at hvL
    exact WithTop.top_ne_coe hvL
  obtain ⟨a, ha, ha'⟩ := exists_depth C hπ hb0
  have hva : C.valuation b = (a : WithTop ℤ) := C.valuation_eq_of_mem_of_notMem ha ha'
  let d (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer) :=
    (N.fieldShift E hN (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  let p (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer)
      (i : Fin q) := N.index hπ (w i) - d N hN * C.index hπ 1
  have hpos (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer) :
      0 < d N hN := N.fieldShift_uniformizer_pos E hN hϖ
  have hc (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer) :
      ScaledLatticeCoordinates N C w (d N hN) (p N hN) :=
    scaledLatticeCoordinates_of_normalizing N C w hN hC hπ hϖ
  have hk := diagonalCriticalExponent L C w (d L hL) (p L hL) hwL (hpos L hL) (hc L hL) ⟨j⟩ b hbN
  rw [hb] at hk
  obtain ⟨k, hline⟩ : ∃ k : ℤ, criticalExponent C b = (k : WithBot ℤ) := by
    cases h : criticalExponent C b with
    | bot =>
      rw [h, WithBot.map_bot] at hk
      exact (WithBot.bot_ne_coe (hk.symm.trans hkL)).elim
    | coe k => exact ⟨k, rfl⟩
  have hrL : r₁ = d L hL * (-k) := by
    rw [hline, WithBot.map_coe] at hk
    have h := WithBot.coe_injective (hkL.symm.trans hk)
    rw [mul_neg, ← h, neg_neg]
  have hnScale (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer)
      (hw : RelSplits (L := E) N w) (n : ℤ) (hv : N.valuation β = ((-n : ℤ) : WithTop ℤ)) :
      n = d N hN * (-a) := by
    have h := valuation_diagonal N C w (d N hN) (p N hN) hw (hpos N hN) (hc N hN) j b
    rw [hb, hva, WithTop.map_coe] at h
    have h' := WithTop.coe_injective (hv.symm.trans h)
    rw [mul_neg, ← h', neg_neg]
  have hnL := hnScale L hL hwL n₁ hvL
  have hnM := hnScale M hM hwM n₂ hvM
  have hlt : -k < -a := by
    apply (mul_lt_mul_iff_right₀ (hpos L hL)).mp
    simpa only [← hrL, ← hnL] using hr₁
  let S : Stratum 𝒪[F] F E := ⟨C, -a, -k, b, hlt, by
    show ((-(-a) : ℤ) : WithTop ℤ) ≤ C.valuation b
    simpa only [neg_neg] using hva.ge⟩
  have hS : S.IsPure := ⟨isField_of_normalizingUnits C hbN, by
    show C.valuation b = ((-(-a) : ℤ) : WithTop ℤ)
    simpa only [neg_neg] using hva⟩
  obtain ⟨Z, hZc, hZn, hZr, hZ, hEq, hram, _⟩ := hApprox F E S hS
  change Z.chain = C at hZc
  change Z.n = -a at hZn
  change Z.r = -k at hZr
  have hZnorm := normalizingUnits_of_isField Z.chain hZ.1.1.1 hZ.1.1.2
  have hZval := hZ.1.2
  have hZcrit := hZ.2
  rw [hZc] at hZnorm hZval hZcrit
  change C.valuation Z.b = ((-Z.n : ℤ) : WithTop ℤ) at hZval
  rw [hZn, neg_neg] at hZval
  rw [hZr, neg_neg] at hZcrit
  let γ := diagonal F w Z.b
  have hdiag (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer)
      (hw : RelSplits (L := E) N w) (n : ℤ) (hn : n = d N hN * (-a)) :
      ∃ Y : Stratum 𝒪[F] F V, Y.chain = N ∧ Y.n = n ∧ Y.r = d N hN * (-k) ∧ Y.b = γ ∧
        Y.IsSimple ∧ criticalExponent N β = ((-Y.r : ℤ) : WithBot ℤ) ∧
        Y.b - β ∈ N.endFiltration (-Y.r) := by
    have hv : N.valuation γ = ((-n : ℤ) : WithTop ℤ) := by
      dsimp only [γ]
      rw [valuation_diagonal N C w (d N hN) (p N hN) hw (hpos N hN) (hc N hN) j,
        hZval, WithTop.map_coe, hn, mul_neg, neg_neg]
    let Y : Stratum 𝒪[F] F V := ⟨N, n, d N hN * (-k), γ,
      hn.symm ▸ mul_lt_mul_of_pos_left hlt (hpos N hN), hv.ge⟩
    refine ⟨Y, rfl, rfl, rfl, rfl, ⟨⟨?_, hv⟩, ?_⟩, ?_, ?_⟩
    · exact isField_of_normalizingUnits N (normalizingUnits_diagonal N C w (d N hN) (p N hN)
        hw (hpos N hN) (hc N hN) j Z.b hZnorm)
    · change criticalExponent N γ < ((-(d N hN * -k) : ℤ) : WithBot ℤ)
      dsimp only [γ]
      rw [diagonalCriticalExponent N C w (d N hN) (p N hN) hw (hpos N hN) (hc N hN) ⟨j⟩ Z.b hZnorm,
        mul_neg, neg_neg]
      cases h : criticalExponent C Z.b with
      | bot => exact WithBot.bot_lt_coe _
      | coe l => exact WithBot.coe_lt_coe.mpr (mul_lt_mul_of_pos_left (WithBot.coe_lt_coe.mp (h ▸ hZcrit)) (hpos N hN))
    · change criticalExponent N β = ((-(d N hN * -k) : ℤ) : WithBot ℤ)
      rw [← hb, diagonalCriticalExponent N C w (d N hN) (p N hN) hw (hpos N hN) (hc N hN) ⟨j⟩ b hbN,
        hline, WithBot.map_coe, mul_neg, neg_neg]
    · change diagonal F w Z.b - β ∈ N.endFiltration (-(d N hN * -k))
      have hDiff : diagonal F w (Z.b - b) = diagonal F w Z.b - β := by rw [map_sub, hb]
      rw [← hDiff, mul_neg, neg_neg,
        diagonal_mem_endFiltration_iff N C w (d N hN) (p N hN) hw (hpos N hN) (hc N hN) j,
        ceilDiv_scale_mul _ (hpos N hN)]
      simpa only [S, hZc, hZr, neg_neg] using Stratum.sub_mem_of_equivalent hEq.symm
  obtain ⟨U, hUc, hUn, hUr, hUb, hUs, hUk, hUd⟩ := hdiag L hL hwL n₁ hnL
  obtain ⟨W, hWc, hWn, hWr, hWb, hWs, hWk, hWd⟩ := hdiag M hM hwM n₂ hnM
  have hperiod (N : LatticeChain 𝒪[F] F V) (hN : ∀ a : Eˣ, subfieldUnits F E V a ∈ N.stabilizer) :
      ((N.period / elementRamificationIndex F β : ℕ) : ℤ) = d N hN := by
    let D := N.subfieldChain E hN
    have hd : (D.period : ℤ) = d N hN := N.subfieldChain_period_eq_shift E hN hϖ
    have hprod := N.fieldShift_uniformizer_mul_ramification E hN hϖ
    change d N hN * (subfieldRamificationIndex F E : ℤ) = (N.period : ℤ) at hprod
    rw [← hd] at hprod
    have hprod' : D.period * subfieldRamificationIndex F E = N.period := by exact_mod_cast hprod
    have he : 0 < subfieldRamificationIndex F E := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, mul_zero] at hprod'
      exact N.period_pos.ne' hprod'.symm
    rw [elementRamificationIndex, dite_eq_left hf, ← hprod', Nat.mul_div_cancel _ he]
    exact hd
  have hramB := (elementInvariants_diagonal L C w (d L hL) (p L hL) hwL (hpos L hL) (hc L hL) j b hbN).1
  have hramG := (elementInvariants_diagonal L C w (d L hL) (p L hL) hwL (hpos L hL) (hc L hL) j Z.b hZnorm).1
  rw [hb] at hramB
  refine ⟨U, W, -k, hUc, hWc, hUn, hWn, hUr.trans hrL.symm, hUb.trans hWb.symm,
    hUs, hWs, hUk, hWk, hUd, hWd, ?_, ?_, ?_⟩
  · rw [hUr, hperiod L hL]
  · rw [hWr, hperiod M hM]
  · rw [hUb, hramG, hramB]
    exact hram

end Langlands.BushnellKutzko
