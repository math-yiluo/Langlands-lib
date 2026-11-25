import Langlands.BaseChange.CyclicAlgebraFullMatchingStatement
import Langlands.BaseChange.CyclicProductConcordance
import Langlands.BaseChange.FinitePlaceFullMatchingStatement

/-!
# Full finite-place matching for a cyclic algebra, from the field case

`cyclicAlgebraFullMatching_of_finitePlaceFullMatching`: the full matching statement for cyclic
field extensions (`FinitePlaceFullMatchingStatement`) implies the one for cyclic algebras
(`CyclicAlgebraFullMatchingStatement`), by the two constructions of `CyclicProductConcordance.lean`
through the field coordinates `E ≃ₐ[F] (Fin (m + 1) → L)`; the vanishing off the norms is the
same condition for `σ` and for `τ` (`vanishesOffNorms_cyclicProduct_iff`). The field `L` lives in
the universe of `E`, so the hypothesis is taken in the same universes. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- **Full matching for a cyclic algebra, from the field case.** -/
theorem cyclicAlgebraFullMatching_of_finitePlaceFullMatching :
    FinitePlaceFullMatchingStatement.{u, v} → CyclicAlgebraFullMatchingStatement.{u, v} := by
  intro hfull F _ _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _
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
  obtain ⟨hdown, hup⟩ := hfull F L τ d n hτ μF μ
  have hσ1 := hσ.pow_eq_one
  constructor
  · intro φ
    obtain ⟨φL, -, htrans⟩ :=
      exists_concordant_ordinary_cyclicProduct c hc hc' hshift hwrap hσ1 hτ μF μ μE hκ φ
    obtain ⟨f, hf⟩ := hdown φL
    exact ⟨f, htrans f hf⟩
  · intro f hf
    have hfL := (vanishesOffNorms_cyclicProduct_iff c hc hc' hshift hwrap hσ1 μF f).mp hf
    obtain ⟨φL, hφL⟩ := hup f hfL
    obtain ⟨φ, hφ⟩ :=
      exists_concordant_twisted_cyclicProduct c hc hc' hshift hwrap hσ1 hτ μF μ μE hκ φL
    exact ⟨φ, hφ f hφL⟩

end Langlands.BaseChange
