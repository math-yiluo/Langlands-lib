import Langlands.LocalField.Normalization.Proof

/-!
# Continuity of the normalized absolute value

The continuity helper formerly private to the root-coordinate finite-function
proof is shared with the scalar Schwartz–Bruhat valuation-bounds proof.
-/

namespace Langlands.PadicField.TopologicalData

universe u

/-- The normalized absolute value is continuous for the supplied topology. -/
theorem continuous_normalizedAbs {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) :
    letI := T.topology
    Continuous T.normalizedAbs := by
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  have habs (x : F.Carrier) :
      T.normalizedAbs x = ‖x‖ ^ Module.finrank (Padic p) F.Carrier :=
    T.normalizedAbs_eq_canonicalNorm_pow_degree x
  simp_rw [show T.normalizedAbs = fun x =>
    ‖x‖ ^ Module.finrank (Padic p) F.Carrier from funext habs]
  exact continuous_norm.pow _

end Langlands.PadicField.TopologicalData
