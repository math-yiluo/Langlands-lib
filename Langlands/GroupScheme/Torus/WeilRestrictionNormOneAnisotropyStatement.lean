import Langlands.GroupScheme.Torus.WeilRestrictionNormOne
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Anisotropy of the actual finite-separable norm-one torus -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.WeilGm

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K]

/-- The actual norm-one group of a finite separable field extension has
split rank zero over the ground field. -/
def normOneAnisotropyStatement : Prop :=
  Algebra.IsSeparable k K →
    IsAnisotropic (normOne (CommRingCat.of k) K)

end Langlands.GroupScheme.WeilGm
