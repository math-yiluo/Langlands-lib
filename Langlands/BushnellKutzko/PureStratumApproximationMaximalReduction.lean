import Langlands.BushnellKutzko.PureStratumApproximationCriticalReduction
import Langlands.BushnellKutzko.PureStratumApproximationDiagonalTransport
import Langlands.BushnellKutzko.CorestrictionChains
import Langlands.BushnellKutzko.RefinementProof

/-! # Reduction of critical-level approximation to a maximal generated field -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV uE

/-- The critical-level approximation assertion when the generated field has full degree
`[F[b]:F] = dim_F V`. In the pure case this means that `V` is a line over `F[b]`. -/
def MaximalCriticalApproximationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsPure → criticalExponent S.chain S.b = ((-S.r : ℤ) : WithBot ℤ) →
    elementDegree F S.b = Module.finrank F V →
    ∃ T : Stratum 𝒪[F] F V,
      T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ T.IsSimple ∧ S.Equivalent T ∧
      elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b ∧
      elementResidueDegree F T.b ∣ elementResidueDegree F S.b

/-- The maximal-generated-field assertion suffices for critical-level approximation. -/
def PureStratumApproximationMaximalReductionStatement : Prop :=
  MaximalCriticalApproximationStatement.{uF, uV} →
    CriticalPureStratumSimpleApproximationStatement.{uF, uV}

section RegularAction

variable {F : Type uF} [Field F] [ValuativeRel F] {E : Type uE} [Field E] [Algebra F E]

omit [ValuativeRel F] in
private theorem elementAlgebra_regular_generator {β : E}
    (hgen : Algebra.adjoin F ({β} : Set E) = ⊤) :
    elementAlgebra (subfieldEmbedding F E E β) = (subfieldEmbedding F E E).range := by
  change Algebra.adjoin F ({subfieldEmbedding F E E β} : Set (Module.End F E)) = _
  rw [← AlgHom.map_adjoin_singleton (subfieldEmbedding F E E) β, hgen, Algebra.map_top]

private theorem normalizingUnits_regular_generator (C : LatticeChain 𝒪[F] F E)
    (hC : ∀ a : Eˣ, subfieldUnits F E E a ∈ C.stabilizer) {β : E}
    (hgen : Algebra.adjoin F ({β} : Set E) = ⊤) :
    NormalizingUnits C (elementAlgebra (subfieldEmbedding F E E β)) := by
  rw [elementAlgebra_regular_generator hgen]
  intro x hx hx0
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx0 (by simp [h])
  exact ⟨subfieldUnits F E E (Units.mk0 a ha), rfl, hC _⟩

omit [ValuativeRel F] in
private theorem elementDegree_regular_generator [FiniteDimensional F E] {β : E}
    (hgen : Algebra.adjoin F ({β} : Set E) = ⊤) :
    elementDegree F (subfieldEmbedding F E E β) = Module.finrank F E := by
  unfold elementDegree
  rw [elementAlgebra_regular_generator hgen]
  exact (AlgEquiv.ofInjective (subfieldEmbedding F E E)
    (subfieldEmbedding F E E).toRingHom.injective).toLinearEquiv.finrank_eq.symm

end RegularAction

private theorem scaled_critical_lt (d : ℤ) (hd : 0 < d) {x : WithBot ℤ} {k : ℤ}
    (hx : x < (k : WithBot ℤ)) : WithBot.map (fun j => d * j) x < ((d * k : ℤ) : WithBot ℤ) := by
  cases x with
  | bot =>
    rw [WithBot.map_bot]
    exact WithBot.bot_lt_coe _
  | coe j =>
    rw [WithBot.map_coe]
    exact WithBot.coe_lt_coe.mpr (mul_lt_mul_of_pos_left (WithBot.coe_lt_coe.mp hx) hd)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Compress to the line of the generated field and lift the maximal-case witness. -/
theorem pureStratumApproximationMaximalReduction :
    PureStratumApproximationMaximalReductionStatement.{uF, uV} := by
  intro hmax F _ _ _ _ V _ _ _ S hS hcrit
  classical
  let A := S.chain
  obtain ⟨⟨hfield, hA⟩, hval⟩ := hS
  let E : Type uV := elementAlgebra S.b
  let : Field E := hfield.toField
  let β : E := elementGenerator S.b
  have hgen : Algebra.adjoin F ({β} : Set E) = ⊤ := adjoin_elementGenerator S.b
  have hβ : subfieldEmbedding F E V β = S.b := subfieldEmbedding_elementGenerator S.b hfield
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  let C : LatticeChain 𝒪[F] F E := subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  have hC : ∀ u : Eˣ, subfieldUnits F E E u ∈ C.stabilizer :=
    subfieldBasisChain_normalized (Module.Basis.singleton Unit E) hϖ
  obtain ⟨q, w, hw⟩ := exists_relSplits_basis A hπ hA
  let : Nontrivial V := A.nontrivialSpace
  let j : Fin q := Classical.choice w.index_nonempty
  let d := (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  let p (i : Fin q) := A.index hπ (w i) - d * C.index hπ 1
  have hd : 0 < d := A.fieldShift_uniformizer_pos E hA hϖ
  have hc : ScaledLatticeCoordinates A C w d p :=
    scaledLatticeCoordinates_of_normalizing A C w hA hC hπ hϖ
  let b : Module.End F E := subfieldEmbedding F E E β
  have hb : diagonal F w b = S.b := by
    change diagonal F w (LinearMap.mulLeft F β) = S.b
    rw [diagonal_mulLeft, hβ]
  have hbn : NormalizingUnits C (elementAlgebra b) := normalizingUnits_regular_generator C hC hgen
  have hb0 : b ≠ 0 := by
    intro h
    have hz : S.b = 0 := by rw [← hb, h, map_zero]
    simp [hz, LatticeChain.valuation] at hval
    exact WithTop.top_ne_coe hval
  -- The two integer parameters are multiples of the relative shift.
  obtain ⟨m, hm, hm'⟩ := exists_depth C hπ hb0
  have hbval : C.valuation b = (m : WithTop ℤ) := C.valuation_eq_of_mem_of_notMem hm hm'
  have hva := valuation_diagonal A C w d p hw hd hc j b
  rw [hb, hbval, WithTop.map_coe] at hva
  change A.valuation S.b = ((d * m : ℤ) : WithTop ℤ) at hva
  have hSn : S.n = d * (-m) := by
    have hn : -S.n = d * m := WithTop.coe_injective (hval.symm.trans hva)
    rw [mul_neg, ← hn, neg_neg]
  have hka := diagonalCriticalExponent A C w d p hw hd hc ⟨j⟩ b hbn
  rw [hb] at hka
  obtain ⟨k, hk⟩ : ∃ k : ℤ, criticalExponent C b = (k : WithBot ℤ) := by
    cases h : criticalExponent C b with
    | bot =>
      rw [h, WithBot.map_bot] at hka
      exact (WithBot.bot_ne_coe (hka.symm.trans hcrit)).elim
    | coe k => exact ⟨k, rfl⟩
  rw [hk, WithBot.map_coe] at hka
  have hSr : S.r = d * (-k) := by
    have hr : -S.r = d * k := WithBot.coe_injective (hcrit.symm.trans hka)
    rw [mul_neg, ← hr, neg_neg]
  have hrn : -k < -m := by
    by_contra! h
    have hn := mul_le_mul_of_nonneg_left h hd.le
    rw [← hSn, ← hSr] at hn
    exact S.r_lt_n.not_ge hn
  let U : Stratum 𝒪[F] F E := ⟨C, -m, -k, b, hrn, by
    show ((-(-m) : ℤ) : WithTop ℤ) ≤ C.valuation b
    rw [neg_neg, hbval]⟩
  have hU : U.IsPure := ⟨isField_of_normalizingUnits C hbn, by
    show C.valuation b = ((-(-m) : ℤ) : WithTop ℤ)
    rw [neg_neg, hbval]⟩
  have hUk : criticalExponent U.chain U.b = ((-U.r : ℤ) : WithBot ℤ) := by
    simpa [U] using hk
  have hUd : elementDegree F U.b = Module.finrank F E := elementDegree_regular_generator hgen
  obtain ⟨G, hGc, hGn, hGr, hG, hUG, he, hf⟩ := hmax F E U hU hUk hUd
  have hGc' : G.chain = C := hGc
  have hGn' : G.n = -m := hGn
  have hGr' : G.r = -k := hGr
  obtain ⟨⟨hGF, hGnorm⟩, hGval⟩ := hG.1
  have hNG := normalizingUnits_of_isField G.chain hGF hGnorm
  rw [hGc'] at hNG hGval
  change C.valuation G.b = ((-G.n : ℤ) : WithTop ℤ) at hGval
  have hTval : A.valuation (diagonal F w G.b) = ((-S.n : ℤ) : WithTop ℤ) := by
    rw [valuation_diagonal A C w d p hw hd hc j G.b, hGval, hGn', neg_neg,
      WithTop.map_coe, hSn, mul_neg, neg_neg]
  let T : Stratum 𝒪[F] F V := ⟨A, S.n, S.r, diagonal F w G.b, S.r_lt_n, hTval.ge⟩
  have hT : T.IsSimple := by
    refine ⟨⟨isField_of_normalizingUnits A
      (normalizingUnits_diagonal A C w d p hw hd hc j G.b hNG), hTval⟩, ?_⟩
    have hGlt := hG.2
    rw [hGc', hGr', neg_neg] at hGlt
    change criticalExponent A (diagonal F w G.b) < ((-S.r : ℤ) : WithBot ℤ)
    rw [diagonalCriticalExponent A C w d p hw hd hc ⟨j⟩ G.b hNG, hSr, mul_neg, neg_neg]
    exact scaled_critical_lt d hd hGlt
  have hEq : S.Equivalent T := by
    apply Stratum.equivalent_of_sub_mem (S := S) (T := T) rfl rfl
    change S.b - diagonal F w G.b ∈ A.endFiltration (-S.r)
    have hb' := congrArg (fun x : Module.End F V => x - diagonal F w G.b) hb
    rw [← hb', ← map_sub, hSr, mul_neg, neg_neg,
      diagonal_mem_endFiltration_iff A C w d p hw hd hc j, ceilDiv_scale_mul d hd]
    simpa [U] using Stratum.sub_mem_of_equivalent hUG
  have hI := elementInvariants_diagonal A C w d p hw hd hc j b hbn
  have hJ := elementInvariants_diagonal A C w d p hw hd hc j G.b hNG
  rw [hb] at hI
  refine ⟨T, rfl, rfl, rfl, hT, hEq, ?_, ?_⟩
  · change elementRamificationIndex F (diagonal F w G.b) ∣ elementRamificationIndex F S.b
    rw [hJ.1, hI.1]
    exact he
  · change elementResidueDegree F (diagonal F w G.b) ∣ elementResidueDegree F S.b
    rw [hJ.2, hI.2]
    exact hf

end Langlands.BushnellKutzko.PureApproximation
