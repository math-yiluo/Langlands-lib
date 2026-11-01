import Langlands.Group.GL.MirabolicMixedOrbitData

/-!
# The two mixed mirabolic orbits, with the open orbit first

This is the geometric statement from Bernstein–Zelevinsky (1977), §7.2,
printed p.471, for the positive-source-rank cases of 4.13(b),(c).
It uses the published inducing subgroups and representative functions
unchanged. It is a proposition definition, not an orbit theorem.
-/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

universe uF

/-- The actual left and right mixed inducing subgroups each have two
disjoint orbits covering the left quotient, ordered with every initial
union open. The complete representative functions are the published ones:
the descending cycle at `0` and the identity at `1`. -/
def MirabolicMixedOrbitCoverageStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  (∀ k r : ℕ,
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI : IsTopologicalGroup (mirabolic (k + r + 2) F.Carrier) := inferInstance
    ∃ s : Geometric.OrderedDoubleCosets
      (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier) 2,
      s.representative = leftRepresentative k r F.Carrier) ∧
  (∀ k r : ℕ,
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI : IsTopologicalGroup (mirabolic (k + r + 2) F.Carrier) := inferInstance
    ∃ s : Geometric.OrderedDoubleCosets
      (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier) 2,
      s.representative = rightRepresentative k r F.Carrier)

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
