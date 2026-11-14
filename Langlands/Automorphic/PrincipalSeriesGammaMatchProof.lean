import Langlands.Automorphic.PrincipalSeriesGammaMatchStatement
import Langlands.Automorphic.PrincipalSeriesAutomorphicGamma
import Langlands.Correspondence.TriangularArithmeticGamma

/-! # Pair gamma comparison for principal-series constituents: proof -/

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

open Correspondence

/-- Both gamma factors are `∏ γ(s, μ_i μ'_j, ψ)`: the representation side by gamma
multiplicativity on the principal series, the arithmetic side by the flags of the
upper triangular bases; the permutations only reorder the factors. -/
theorem principalSeriesPairGammaMatchStatement :
    PrincipalSeriesPairGammaMatchStatement.{u, uV, uE} := by
  intro p _ K eC ε hε e h ψ r t μ μ' π π' X Y ⟨A, hAπ, hA, hsA⟩ ⟨A', hAπ', hA', hsA'⟩
    ⟨B, hBX, hN, hB, b, σ, hbB⟩ ⟨B', hBY, hN', hB', b', σ', hbB'⟩
  subst hAπ hAπ' hBX hBY
  refine ⟨⟨localSelfDualHaar K ψ, isSelfDual_localSelfDualHaar K ψ⟩, fun ν hν => ?_⟩
  refine ⟨∏ j, ∏ i, tateRationalGamma K ψ ν (μ i * μ' j),
    isAutomorphicPairGammaFactor_principalSeries K ψ ν hν μ μ' A A' hA hsA hA' hsA', ?_⟩
  have hG := isArithmeticPairGammaFactor_triangular K eC ε hε e h ψ ν hν
    (fun i => μ (σ i)) (fun j => μ' (σ' j)) B B' hN hN' hB hB' b b'
    (fun g => (hbB g).1) (fun g => (hbB' g).1) (fun g i => (hbB g).2 i)
    (fun g j => (hbB' g).2 j)
  have hre : ∏ i, ∏ j, tateRationalGamma K ψ ν (μ (σ i) * μ' (σ' j)) =
      ∏ j, ∏ i, tateRationalGamma K ψ ν (μ i * μ' j) :=
    calc ∏ i, ∏ j, tateRationalGamma K ψ ν (μ (σ i) * μ' (σ' j))
        = ∏ j, ∏ i, tateRationalGamma K ψ ν (μ (σ i) * μ' (σ' j)) := Finset.prod_comm
      _ = ∏ j, ∏ i, tateRationalGamma K ψ ν (μ (σ i) * μ' j) :=
        Equiv.prod_comp σ' fun j => ∏ i, tateRationalGamma K ψ ν (μ (σ i) * μ' j)
      _ = ∏ j, ∏ i, tateRationalGamma K ψ ν (μ i * μ' j) :=
        Finset.prod_congr rfl fun j _ =>
          Equiv.prod_comp σ fun i => tateRationalGamma K ψ ν (μ i * μ' j)
  rwa [hre] at hG

end Langlands.ClassField.Global.RelativeWeilGroup
