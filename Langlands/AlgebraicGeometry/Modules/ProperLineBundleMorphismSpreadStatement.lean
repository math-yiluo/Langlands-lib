import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Spreading invertibility of an actual line-bundle section -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

/-- An actual line-bundle section that is a frame on one scheme-theoretic
fibre is a frame over a neighbourhood of that point when the structure map
is universally closed. -/
def ProperLineBundleMorphismSpreadStatement : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S),
    UniversallyClosed f →
    ∀ (L : LineBundle X)
      (φ : Langlands.Scheme.Modules.structureSheaf X ⟶ L.obj) (s : S),
      IsIso ((Scheme.Modules.pullback (f.fiberι s)).map φ) →
      ∃ U : S.Opens, s ∈ U ∧
        IsIso ((Scheme.Modules.pullback (pullback.fst f U.ι)).map φ)

end Langlands.AlgebraicGeometry.Modules
