import Langlands.BushnellKutzko.SimpleCharacterResidueComparisonStatement
import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement
import Langlands.BushnellKutzko.PureStratumSimpleApproximationStatement
import Langlands.BushnellKutzko.HeisenbergIntertwiningFactor
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences
import Langlands.BushnellKutzko.CentralizerDoubleCoset
import Langlands.BushnellKutzko.CentralizerResidueComparison

/-! # Reduction of the residue comparison of BK94 (5.2) to the intertwining of simple
characters (BK93 (3.3.2)) -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

/-- The approximation theorem BK93 (2.4.1), the nonemptiness of the sets of simple
characters BK93 (3.3.21) and their intertwining BK93 (3.3.2) imply the residue comparison
of BK94 (5.2). -/
def SimpleCharacterResidueComparisonReductionStatement : Prop :=
  PureStratumSimpleApproximationStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} →
  SimpleCharacterIntertwiningStatement.{uF, uV} →
  SimpleCharacterResidueComparisonStatement.{uF, uV}

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a field `F[β]`, the lattice `𝔓^t ∩ B_β` consists of the `F[β]`-linear elements of
`𝔓^t`. -/
theorem centralizerLattice_eq_inf_fieldCommutant (L : LatticeChain 𝒪[F] F V) {β : A}
    (hf : IsField (elementAlgebra β)) (t : ℤ) :
    letI := hf.toField
    centralizerLattice L β t =
      L.endFiltration t ⊓ StratumEquivalence.fieldCommutant (elementAlgebra β) := by
  let _ := hf.toField
  ext x
  simp only [centralizerLattice, Submodule.mem_inf, LinearMap.mem_ker,
    StratumEquivalence.adjointMap_apply, sub_eq_zero]
  refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx => ?_⟩
  · intro a v
    have hle : elementAlgebra β ≤ Subalgebra.centralizer F {x} := by
      apply Algebra.adjoin_le
      rintro _ rfl
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hx.symm
    have ha := hle a.2
    rw [Subalgebra.mem_centralizer_iff] at ha
    change x ((a : Module.End F V) v) = (a : Module.End F V) (x v)
    exact LinearMap.congr_fun (ha x rfl) v
  · have hx' : ∀ (a : elementAlgebra β) (v : V), x (a • v) = a • x v := hx
    ext v
    exact (hx' ⟨β, Algebra.self_mem_adjoin_singleton F β⟩ v).symm

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A simple stratum at depth `0` has positive critical depth. -/
theorem zero_lt_simpleCriticalDepth_of_isSimple {S : Stratum 𝒪[F] F V} (hr : S.r = 0)
    (hS : S.IsSimple) : (((0 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
  have h := hS.2
  rw [hr, neg_zero] at h
  cases hc : criticalExponent S.chain S.b using WithBot.recBotCoe with
  | bot => simp [simpleCriticalDepth, hc]
  | coe j =>
    rw [hc] at h
    have hj : j < 0 := WithBot.coe_lt_coe.mp h
    have he : simpleCriticalDepth S.chain S.b = ((-j : ℤ) : WithTop ℤ) := by
      rw [simpleCriticalDepth, hc]
    rw [he, Nat.cast_zero, WithTop.coe_lt_coe]
    omega

/-- **BK94 (5.8).** Two simple strata `[𝔄,n,0,γ_i]` with the same simple characters have
`𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for every `t ∈ ℤ`, where `𝔔_i^t = 𝔓^t ∩ B_{γ_i}`. -/
theorem centralizerLattice_sup_eq_of_pairs_eq
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hRes : SimpleCharacterRestrictionStatement.{uF, uV})
    (hInt : SimpleCharacterIntertwiningStatement.{uF, uV})
    [FiniteDimensional F V] (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {L : LatticeChain 𝒪[F] F V} {n : ℤ} (S₁ S₂ : SimpleStratumAt L n 0)
    (hC : simpleCharacterPairs ψF S₁.1 0 = simpleCharacterPairs ψF S₂.1 0) (t : ℤ) :
    centralizerLattice L S₁.1.b t ⊔ L.endFiltration (t + 1) =
      centralizerLattice L S₂.1.b t ⊔ L.endFiltration (t + 1) := by
  have hr₁ : S₁.1.r = 0 := S₁.2.2.2.1
  have hr₂ : S₂.1.r = 0 := S₂.2.2.2.1
  have hs₁ := S₁.2.2.2.2
  have hs₂ := S₂.2.2.2.2
  have hn₁ : ((0 : ℕ) : ℤ) < S₁.1.n := by have := S₁.1.r_lt_n; omega
  have hn₂ : ((0 : ℕ) : ℤ) < S₂.1.n := by have := S₂.1.r_lt_n; omega
  -- A common simple character `θ`.
  obtain ⟨q₁, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox S₁.1 hs₁
  obtain ⟨θ₁, hθ₁⟩ := (hRes F V ψF hψ S₁.1 hr₁ hs₁ q₁).2.2.2.2 0 hn₁
  have hp : (⟨_, θ₁⟩ : CharacterPair G) ∈ simpleCharacterPairs ψF S₁.1 0 :=
    Set.mem_iUnion.mpr ⟨q₁, θ₁, hθ₁, rfl⟩
  rw [hC] at hp
  obtain ⟨q₂, θ₂, hθ₂, hpair⟩ := Set.mem_iUnion.mp hp
  have hI : characterSelfIntertwining θ₂ = characterSelfIntertwining θ₁ :=
    congrArg (fun p : CharacterPair G => characterSelfIntertwining p.2) hpair
  -- Its intertwining is `J_i¹ B_i^× J_i¹` for both strata.
  have hI₁ := (hInt F V ψF hψ S₁.1 hr₁ hs₁ q₁ 0 hn₁
    (zero_lt_simpleCriticalDepth_of_isSimple hr₁ hs₁) θ₁ hθ₁).1
  have hI₂ := (hInt F V ψF hψ S₂.1 hr₂ hs₂ q₂ 0 hn₂
    (zero_lt_simpleCriticalDepth_of_isSimple hr₂ hs₂) θ₂ hθ₂).1
  have hY₁ := simpleCharacterIntertwiningFactor_mul_centralizer_zero
    simpleStratumGroupProperties S₁.1 hr₁ hs₁ q₁
  have hY₂ := simpleCharacterIntertwiningFactor_mul_centralizer_zero
    simpleStratumGroupProperties S₂.1 hr₂ hs₂ q₂
  dsimp only at hI₁ hI₂ hY₁ hY₂
  have hJ₁ : simpleJGroup S₁.1.chain S₁.1.n S₁.1.b q₁.tail 1 ≤ L.unitFiltration 1 :=
    (simpleJGroup_le_unitFiltration _ _ _ _ _).trans
      (le_of_eq (congrArg (fun L' : LatticeChain 𝒪[F] F V => L'.unitFiltration 1) S₁.2.1))
  have hJ₂ : simpleJGroup S₂.1.chain S₂.1.n S₂.1.b q₂.tail 1 ≤ L.unitFiltration 1 :=
    (simpleJGroup_le_unitFiltration _ _ _ _ _).trans
      (le_of_eq (congrArg (fun L' : LatticeChain 𝒪[F] F V => L'.unitFiltration 1) S₂.2.1))
  refine centralizerLattice_sup_eq_of_doubleCoset_eq L S₁.1.b S₂.1.b _ _ hJ₁ hJ₂ ?_ t
  rw [← hY₁, ← hY₂, ← hI₁, ← hI₂, hI]

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1000000 in
/-- **Reduction of BK94 (5.2).** -/
theorem simpleCharacterResidueComparisonReduction :
    SimpleCharacterResidueComparisonReductionStatement.{uF, uV} := by
  intro hApprox hRes hInt F _ _ _ _ V _ _ _ ψF hψ L n S₁ S₂ hC
  have h58 := centralizerLattice_sup_eq_of_pairs_eq hApprox hRes hInt ψF hψ S₁ S₂ hC
  refine ⟨by have h := h58 0; rwa [zero_add] at h, fun h₁ h₂ => ?_⟩
  letI := h₁.toField
  letI := h₂.toField
  have : FiniteDimensional F (elementAlgebra S₁.1.b) :=
    L.finiteDimensional_subfield (elementAlgebra S₁.1.b)
  have : FiniteDimensional F (elementAlgebra S₂.1.b) :=
    L.finiteDimensional_subfield (elementAlgebra S₂.1.b)
  obtain ⟨hf₁, hn₁⟩ := S₁.2.2.2.2.1.1
  obtain ⟨hf₂, hn₂⟩ := S₂.2.2.2.2.1.1
  have hE₁ : ∀ a : (elementAlgebra S₁.1.b)ˣ,
      subfieldUnits F (elementAlgebra S₁.1.b) V a ∈ L.stabilizer := by
    intro a
    have h := hn₁ a
    rwa [S₁.2.1] at h
  have hE₂ : ∀ a : (elementAlgebra S₂.1.b)ˣ,
      subfieldUnits F (elementAlgebra S₂.1.b) V a ∈ L.stabilizer := by
    intro a
    have h := hn₂ a
    rwa [S₂.2.1] at h
  have hG : GradedCentralizer.GradedEq L (elementAlgebra S₁.1.b) (elementAlgebra S₂.1.b) := by
    intro t
    have e₁ : centralizerLattice L S₁.1.b t = L.endFiltration t ⊓
        StratumEquivalence.fieldCommutant (elementAlgebra S₁.1.b) :=
      centralizerLattice_eq_inf_fieldCommutant L h₁ t
    have e₂ : centralizerLattice L S₂.1.b t = L.endFiltration t ⊓
        StratumEquivalence.fieldCommutant (elementAlgebra S₂.1.b) :=
      centralizerLattice_eq_inf_fieldCommutant L h₂ t
    rw [← e₁, ← e₂]
    exact h58 t
  refine ⟨fun a => ?_, fun b => ?_, GradedCentralizer.exists_primeElement_congr L hE₁ hE₂ hG, ?_⟩
  · obtain ⟨b, hb, hab⟩ := GradedCentralizer.exists_integer_sub_mem L hE₁ hE₂ hG a.2
    exact ⟨⟨b, hb⟩, hab⟩
  · obtain ⟨a, ha, hba⟩ := GradedCentralizer.exists_integer_sub_mem L hE₂ hE₁ hG.symm b.2
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← neg_sub]
    exact neg_mem hba
  · obtain ⟨s₁, s₂, hs⟩ := GradedCentralizer.exists_tameCorestriction_congr L hE₁ hE₂ hG
    refine ⟨s₁, s₂, fun k x hx => ?_⟩
    have h := hs (-(k + 1)) x hx
    rwa [show -(k + 1) + 1 = -k by ring] at h

end Langlands.BushnellKutzko
