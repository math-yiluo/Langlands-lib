import Langlands.GroupScheme.Reductive.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Actual adjoint-stable realization of a connected reductive group -/

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every connected reductive group over an arbitrary real or complex field
admits a scheme-theoretic closed matrix representation whose full actual
rational-point range is stable under conjugate transpose. -/
def ConnectedReductiveSelfAdjointRealizationStatement : Prop :=
  ∀ (k : Type u) [RCLike k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∃ (d : ℕ) (ρ : MatrixRepresentation G (Fin d)),
      IsClosedSubgroup ρ ∧
      ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
        star q ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range

end Langlands.GroupScheme
