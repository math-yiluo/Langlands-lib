import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Ampleness is preserved by pullback along quasi-finite separated morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `f : X ⟶ Y` be quasi-finite and separated in the sense of the Stacks Project:
locally of finite type, locally quasi-finite, quasi-compact and separated. If a line bundle
`M` on `Y` is ample, then its actual pullback along `f` is ample. This proposition is a
statement, not a proof of it. -/
def QuasiFiniteAmplePullbackStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : LineBundle Y),
    LocallyOfFiniteType f → LocallyQuasiFinite f → QuasiCompact f → IsSeparated f →
      M.IsAmple → ((LineBundle.pullback f).obj M).IsAmple

end Langlands.AlgebraicGeometry.Picard
