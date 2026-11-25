import Langlands.BaseChange.CyclicAlgebraNearIdentityMatchingStatement
import Langlands.BaseChange.CyclicProductConcordance
import Langlands.BaseChange.NearIdentityMatching
import Langlands.Topology.LocallyProfiniteProof

/-!
# Matching of test functions near the identity for a cyclic algebra

Proof of `CyclicAlgebraNearIdentityMatchingStatement` (`cyclicAlgebraNearIdentityMatching`) by
reduction to the field case `nearIdentityMatching` through the field coordinates
`E ≃ₐ[F] (Fin (m + 1) → L)` of the cyclic algebra (`exists_cyclicAlgebraFieldCoordinates`, `L`
with its module topology over `F`), a Haar measure `μ` of `GL_n(L)` whose product the coordinates
carry to `μE` (`exists_isHaarMeasure_measurePreserving_pi`), and the two constructions of
`CyclicProductConcordance.lean`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- **Matching near the identity** for a cyclic algebra: with `E ≅ L^{m+1}` and `κ` the
coordinates on `GL_n`, `U = κ⁻¹(K₀^{m+1})` for a compact open subgroup `K₀` of `GL_n(L)` inside the
neighbourhood of the field case for `L / F`, and `V` the neighbourhood of the field case. -/
theorem cyclicAlgebraNearIdentityMatching : CyclicAlgebraNearIdentityMatchingStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _
  obtain ⟨L, _, _, m, d, τ, c, hl, hτ, hshift, hwrap⟩ := exists_cyclicAlgebraFieldCoordinates hσ
  subst hl
  let : TopologicalSpace L := moduleTopology F L
  have : IsModuleTopology F L := ⟨rfl⟩
  have : Module.Finite F L := hτ.1
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing F L
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  let : MeasurableSpace (GeneralLinear n L) := borel _
  have : BorelSpace (GeneralLinear n L) := ⟨rfl⟩
  let := LocalFieldTopology.t2Space F
  let := LocalFieldTopology.secondCountableTopology F
  let := LocalFieldTopology.totallyDisconnectedSpace F
  have hp := generalLinear_isLocallyProfinite_of_finiteAlgebra (F := F) (E := L) n
  have : LocallyCompactSpace (GeneralLinear n L) := hp.locallyCompactSpace
  have : SecondCountableTopology (GeneralLinear n L) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := L) n
  let κ := cyclicProductGLCoordinates (n := n) c hc hc'
  obtain ⟨μ, hμ, hκ⟩ := exists_isHaarMeasure_measurePreserving_pi κ μE
  obtain ⟨⟨UL, hUL, hUmatch⟩, ⟨VL, hVL, hVmatch⟩⟩ := nearIdentityMatching F L τ d n hτ μF μ
  have hσ1 := hσ.pow_eq_one
  constructor
  · obtain ⟨K₀, hK₀c, hK₀U⟩ :=
      ((Topology.LocallyProfiniteProof.vanDantzig (GeneralLinear n L)).mp hp).2 UL hUL
    refine ⟨κ ⁻¹' Set.pi Set.univ (fun _ => (K₀ : Set (GeneralLinear n L))), ?_, ?_⟩
    · refine ((isOpen_set_pi Set.finite_univ fun _ _ => K₀.isOpen).preimage
        (map_continuous κ)).mem_nhds ?_
      rw [Set.mem_preimage, map_one]
      exact fun i _ => K₀.one_mem
    · intro φ hφ
      obtain ⟨φL, hsupp, htrans⟩ :=
        exists_concordant_ordinary_cyclicProduct c hc hc' hshift hwrap hσ1 hτ μF μ μE hκ φ
      obtain ⟨f, hf⟩ := hUmatch φL ((hsupp K₀.toSubgroup hφ).trans hK₀U)
      exact ⟨f, htrans f hf⟩
  · refine ⟨VL, hVL, fun f hf => ?_⟩
    obtain ⟨φL, hφL⟩ := hVmatch f hf
    obtain ⟨φ, hφ⟩ :=
      exists_concordant_twisted_cyclicProduct c hc hc' hshift hwrap hσ1 hτ μF μ μE hκ φL
    exact ⟨φ, hφ f hφL⟩

end Langlands.BaseChange
