import Langlands.BushnellKutzko.DiagonalPositiveSplitType
import Langlands.BushnellKutzko.PureStratumApproximationAssembly
import Langlands.BushnellKutzko.TameCorestrictionProof

/-! # Split types of level `(x, y)` for `x > y > 0` -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- The stratum `[𝔅,m,m−1,s(c)]` on the centralizer chain for a tame corestriction `s`
and `c ∈ 𝔓^{-m}`. The image formula for `s` supplies the valuation bound. -/
def LatticeChain.corestrictedStratum (L : LatticeChain 𝒪[F] F V)
    {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    [FiniteDimensional F E] (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (s : TameCorestriction 𝒪[F] F E V) (m : ℤ) (c : L.endFiltration (-m)) :
    Stratum (subfieldIntegers F E) E V where
  chain := L.subfieldChain E hE
  n := m
  r := m - 1
  b := s c
  r_lt_n := by omega
  valuation_ge := by
    let := L.finiteDimensional
    have hc : s (c : Module.End F V) ∈ s '' (L.endFiltration (-m) : Set _) :=
      ⟨c, c.2, rfl⟩
    rw [(tameCorestriction F V E).2.2 s L hE (-m)] at hc
    rw [PureApproximation.valuation_subfieldChain L hE]
    exact_mod_cast PureApproximation.le_valuation_of_mem L hc

/-- **BK93 (8.1.3).** The type of level `(x,y)` with `x > y > 0` on `H^m(β,𝔄)` is
the simple character `θ ∈ C(𝔄,m−1,β)` times `ψ_c`, with a split fundamental
corestricted stratum on the centralizer chain and `gcd(m, e(𝔅 | 𝔬_E)) = 1`. -/
def IsUnequalPositiveSplitType {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {K : Subgroup (Module.End F V)ˣ} (ψF : AddChar F ℂ) (x y : ℚ)
    (ρ : Representation ℂ K W) : Prop :=
  ∃ (hψ : IsBKAdditiveCharacter ψF) (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice)
    (j : ℕ) (hS : S.IsSimple),
    S.r = (j : ℤ) + 1 ∧ x = (S.n : ℚ) / S.chain.period ∧ y = (S.r : ℚ) / S.chain.period ∧
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    let L_E := S.chain.subfieldChain E hS.1.1.snd
    Nat.Coprime (j + 1) L_E.period ∧
    ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail j,
    ∃ (c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ))) (s : TameCorestriction 𝒪[F] F E V),
      (S.chain.corestrictedStratum hS.1.1.snd s (j + 1 : ℕ) c).IsSplit ∧
      IsPairIsomorphic ρ (characterRepresentation (θ *
        (filtrationTraceCharacter S.chain ψF hψ (Nat.succ_pos j) c.2).comp
          (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (j + 1)))))

end Langlands.BushnellKutzko
