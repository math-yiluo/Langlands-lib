import Langlands.BushnellKutzko.PureStratumApproximationImprovementSteps
import Langlands.BushnellKutzko.PureStratumSimpleApproximationProof
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences

/-! # Simple strata on other chains normalized by the parameter field -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  [FiniteDimensional F E] {V : Type uV} [AddCommGroup V] [Module F V] [Module E V]
  [IsScalarTower F E V]

/-- The parameter admits a depth-zero simple stratum on `D`, with a defining
sequence that begins at that stratum and remains on `D`. -/
def HasDepthZeroStratumChoice (D : LatticeChain 𝒪[F] F V) (b : Module.End F V) : Prop :=
    ∃ (n : ℤ) (hn : 0 < n) (hv : (-n : WithTop ℤ) ≤ D.valuation b),
      let T : Stratum 𝒪[F] F V := ⟨D, n, 0, b, hn, hv⟩
      T.IsSimple ∧ ∃ q : T.DefiningSequenceChoice,
        q.terms 0 = T ∧ ∀ i, (q.terms i).chain = T.chain

/-- On another chain normalized by the same parameter field there is a simple
depth-zero stratum with the same parameter and an exact defining sequence. -/
theorem exists_depthZeroStratumChoice (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) (hr : S.r = 0)
    {β : E} (hb : subfieldEmbedding F E V β = S.b)
    (hβ : Algebra.adjoin F ({β} : Set E) = ⊤)
    (D : LatticeChain 𝒪[F] F V) (hD : ∀ a : Eˣ, subfieldUnits F E V a ∈ D.stabilizer) :
    HasDepthZeroStratumChoice D S.b := by
  obtain ⟨⟨L, n, r, b, hn, hv⟩, hL, hr', hb', ht, -⟩ :=
    PureApproximation.exists_simple_of_normalized S hS hb hβ D hD (ρ := 0) (by rw [hr]; simp)
  change L = D at hL
  change r = 0 at hr'
  change b = S.b at hb'
  subst L r b
  refine ⟨n, hn, hv, ht, ?_⟩
  exact Stratum.exists_exact_definingSequenceChoice pureStratumSimpleApproximation _ ht

end Langlands.BushnellKutzko.SplitTypeJacquet
