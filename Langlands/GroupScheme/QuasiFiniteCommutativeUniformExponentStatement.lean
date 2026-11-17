import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # A uniform exponent for quasi-finite commutative groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- SGA 3, Exposé IX, Lemma 6.1: a commutative group scheme of finite
presentation that is quasi-finite over a quasi-compact base has one positive
exponent on all scheme-valued points. -/
def QuasiFiniteCommutativeUniformExponentStatement : Prop :=
  ∀ (S : Scheme.{u}) (K : GroupScheme S),
    CompactSpace S → IsCommMonObj K.X →
    LocallyOfFinitePresentation K.X.hom → QuasiCompact K.X.hom →
    QuasiSeparated K.X.hom → LocallyQuasiFinite K.X.hom →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over S) (x : T ⟶ K.X), x ^ n = 1

end Langlands.GroupScheme
