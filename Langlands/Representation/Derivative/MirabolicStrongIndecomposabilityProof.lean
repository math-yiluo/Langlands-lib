import Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityStatement
import Langlands.Representation.Derivative.MirabolicDerivativeVanishing
import Langlands.Representation.Derivative.MirabolicHighestLayerProof
import Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferProof

/-! # Positive level and strong indecomposability of the highest derivative

Positive level follows from the general mirabolic derivative detection theorem.
The highest-layer theorem identifies the entire subrepresentation lattice of the
actual highest derivative with the interval below one nonzero invariant subspace.
The essential-interval criterion then gives the strong indecomposability reduction.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Positive mirabolic derivative level and the highest-derivative criterion for
intrinsic strong indecomposability. -/
theorem mirabolicStrongIndecomposabilityReduction :
    MirabolicStrongIndecomposabilityReduction.{uF, uV} F T := by
  let := T.topology
  intro ψ N A
  constructor
  · exact Mirabolic.derivativeDetection F T ψ N A
  · intro k hk hA hlevel
    obtain ⟨U, hU, ⟨e⟩, hhom⟩ := mirabolicHighestLayer F T ψ N A k hk hA hlevel
    have htransfer :=
      (Classification.strongIndecomposabilityLatticeTransfer.{0, uF, uF, uV, uV}
        ℂ (GeneralLinear.mirabolic N F.Carrier)
        (GeneralLinear (N + 1 - k) F.Carrier)
        A ((mirabolicDerivativeOfOrder T ψ N k hk).obj A)
        A.representation ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation).2
          U hU e
    exact htransfer.trans (and_congr hhom.symm Iff.rfl)

end Langlands.Derivative
