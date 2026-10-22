import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RepresentationTheory.Irreducible

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every equivariant endomorphism of an irreducible complex representation of
at most countable algebraic dimension is multiplication by a unique scalar. -/
def CountableDimensionalSchurStatement : Prop :=
  ∀ (rho : Representation ℂ G V),
    Module.rank ℂ V ≤ Cardinal.aleph0 →
    rho.IsIrreducible →
    ∀ f : rho.IntertwiningMap rho,
      ∃! c : ℂ, f = c • Representation.IntertwiningMap.id rho

end Langlands
