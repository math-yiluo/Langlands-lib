import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitData
import Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding MirabolicMixedOrbitCoverageStatement isTopologicalRing_of_topologicalData
universe uF

/-- The actual left and right mixed inducing subgroups each have two
disjoint orbits covering the left quotient, ordered with every initial
union open. The complete representative functions are the published ones:
the descending cycle at `0` and the identity at `1`. -/
def MirabolicMixedOrbitCoverageStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  (∀ k r : ℕ,
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI : IsTopologicalGroup (Langlands.GeneralLinear.mirabolic (k + r + 2) F.Carrier) := inferInstance
    ∃ s : Geometric.OrderedDoubleCosets
      (leftInducing k r F.Carrier) (Langlands.GeneralLinear.Mirabolic.plusSubgroup (k + r + 1) F.Carrier) 2,
      s.representative = leftRepresentative k r F.Carrier) ∧
  (∀ k r : ℕ,
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI : IsTopologicalGroup (Langlands.GeneralLinear.mirabolic (k + r + 2) F.Carrier) := inferInstance
    ∃ s : Geometric.OrderedDoubleCosets
      (rightInducing k r F.Carrier) (Langlands.GeneralLinear.Mirabolic.plusSubgroup (k + r + 1) F.Carrier) 2,
      s.representative = rightRepresentative k r F.Carrier)

end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
