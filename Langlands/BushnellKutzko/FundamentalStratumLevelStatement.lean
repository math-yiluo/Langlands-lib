import Langlands.BushnellKutzko.NormalizedLevel

/-! # A fundamental stratum computes the normalized level (statement L1)

Bushnell–Kutzko (1993), Introduction, printed p. 8, and (2.3.1)–(2.3.2), printed p. 57;
Bushnell (1987), Theorem 1 (printed p. 192), Remark (2.9) (printed p. 195) and Theorem 2′
(printed pp. 196–197). -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

section Instances

/-! The canonical instances have module-specific names, so that the sibling statement modules
of this namespace can be imported together. -/

local instance fundamentalStratumLevelTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance fundamentalStratumLevelValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance fundamentalStratumLevelTopologicalSpaceGL {p : ℕ} [Fact p.Prime]
    (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **L1.** Let `K : PadicField p`, `n ≥ 1`, `ψ` an additive character of `K` of level one,
`a` a class of irreducible admissible complex representations of `GL_n(K)`, `𝓛` an
`𝔬_K`-lattice chain in `K^n`, `m ≥ 1` and `b ∈ 𝔓^{-m}(𝓛)`. If the stratum
`[𝔄(𝓛), m, m - 1, b]` is fundamental (the coset `b + 𝔓^{1-m}(𝓛)` contains no nilpotent
element) and `a` contains it, then the normalized level of `a` is `m / e(𝓛)`. -/
def FundamentalStratumLevelStatement.{uK, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ), 1 ≤ n →
    ∀ (ψ : AddChar K.Carrier ℂ), IsLevelOne K ψ →
    ∀ (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier))
      (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) (m : ℕ)
      (b : Module.End K.Carrier (Fin n → K.Carrier)),
      1 ≤ m → b ∈ 𝓛.endFiltration (-(m : ℤ)) →
      (∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ¬ IsNilpotent (b + y)) →
      ContainsStratum K n ψ a 𝓛 m b →
      IsNormalizedLevel K n a ((m : ℚ) / (𝓛.period : ℚ))

end Instances

end Langlands.BushnellKutzko
