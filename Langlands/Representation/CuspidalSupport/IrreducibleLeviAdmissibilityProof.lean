import Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityStatement
import Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-!
# Admissibility of irreducible smooth product-Levi representations

The normalized refined quasicuspidal embedding reduces the exact target to
quasicuspidal Levi admissibility, admissibility of normalized refined induction,
and admissibility transfer along an injective intertwiner.
-/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Every irreducible smooth complex representation of an actual product Levi
is admissible, for arbitrary topological data and all ranks. -/
theorem irreducibleLeviAdmissibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IrreducibleLeviAdmissibilityTheorem.{uF, uV} F T := by
  let := T.topology
  intro n B ω hω
  let := T.leviTopologicalGroup B
  obtain ⟨S, σ, hσirr, hσq, j, hj⟩ :=
    normalizedRefinedQuasicuspidalEmbedding.{uF, uV} F T n B ω hω
  have hσadm : σ.IsAdmissible :=
    LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T
      (B.flatten S) σ hσirr hσq
  have hτadm : IsAdmissible (σ.representation.comp
      (Geometric.flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) :=
    (Parabolic.isAdmissible_flattenedLeviTransport_iff F T B S σ.representation).mpr hσadm
  have hIndadm := Parabolic.normalizedRefinedInductionAdmissibility F T B S _ hτadm
  exact isAdmissible_of_injective j hj hIndadm

/-- The specialization to the saturated carrier universe. -/
example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IrreducibleLeviAdmissibilityTheorem.{uF, max uF uV} F T :=
  irreducibleLeviAdmissibility.{uF, max uF uV} F T

end Langlands.CuspidalSupport
