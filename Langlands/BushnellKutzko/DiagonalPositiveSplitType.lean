import Langlands.BushnellKutzko.AdditiveDualityProof
import Langlands.BushnellKutzko.FundamentalStratum
import Langlands.BushnellKutzko.PureStratumApproximationCandidateBound
import Langlands.BushnellKutzko.PairConjugation
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Split types of level `(x, x)` for `x > 0` -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

private theorem exists_filtrationTraceCharacter (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {m : ℕ} (hm : 0 < m)
    {b : Module.End F V} (hb : b ∈ L.endFiltration (-(m : ℤ))) :
    ∃ χ : L.unitFiltration m →* ℂˣ,
      (∀ g, (χ g : ℂ) = elementCharacter (traceCharacter ψF) b g) ∧
      ∀ g : L.unitFiltration m, (g : (Module.End F V)ˣ) ∈ L.unitFiltration (m + 1) → χ g = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact ((additiveDuality F V L ψF hψ.1 hψ.2).2 (k + 1) k (by omega) (by omega)).1 b hb

/-- The character `ψ_b` on `U^m(𝔄)` supplied by additive duality for `b ∈ 𝔓^{-m}` and `m > 0`. -/
def filtrationTraceCharacter (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {m : ℕ} (hm : 0 < m)
    {b : Module.End F V} (hb : b ∈ L.endFiltration (-(m : ℤ))) :
    L.unitFiltration m →* ℂˣ :=
  (exists_filtrationTraceCharacter L ψF hψ hm hb).choose

theorem filtrationTraceCharacter_apply (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {m : ℕ} (hm : 0 < m)
    {b : Module.End F V} (hb : b ∈ L.endFiltration (-(m : ℤ))) (g : L.unitFiltration m) :
    (filtrationTraceCharacter L ψF hψ hm hb g : ℂ) = elementCharacter (traceCharacter ψF) b g :=
  (exists_filtrationTraceCharacter L ψF hψ hm hb).choose_spec.1 g

theorem filtrationTraceCharacter_eq_one (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {m : ℕ} (hm : 0 < m)
    {b : Module.End F V} (hb : b ∈ L.endFiltration (-(m : ℤ))) (g : L.unitFiltration m)
    (hg : (g : (Module.End F V)ˣ) ∈ L.unitFiltration (m + 1)) :
    filtrationTraceCharacter L ψF hψ hm hb g = 1 :=
  (exists_filtrationTraceCharacter L ψF hψ hm hb).choose_spec.2 g hg

/-- **BK93 (8.1.1).** The pair is `(U^n(𝔄), ψ_b)` for a split fundamental stratum
`[𝔄,n,n−1,b]` with `n > 0`, `gcd(n, e(𝔄)) = 1` and `x = n/e(𝔄)`. -/
def IsDiagonalPositiveSplitType {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {K : Subgroup (Module.End F V)ˣ} (ψF : AddChar F ℂ) (x : ℚ)
    (ρ : Representation ℂ K W) : Prop :=
  ∃ (hψ : IsBKAdditiveCharacter ψF) (S : Stratum 𝒪[F] F V) (hn : 0 < S.n),
    S.IsSplit ∧ Nat.Coprime S.n.toNat S.chain.period ∧ x = (S.n : ℚ) / S.chain.period ∧
    IsPairIsomorphic ρ (characterRepresentation
      (filtrationTraceCharacter S.chain ψF hψ (m := S.n.toNat) (by omega) (b := S.b) (by
        rw [Int.toNat_of_nonneg hn.le]
        exact PureApproximation.mem_endFiltration_of_le_valuation S.chain
          (by exact_mod_cast S.valuation_ge))))

end Langlands.BushnellKutzko
