import Langlands.GroupScheme.CoalgebraUnipotence.Definitions

universe u v w

namespace Langlands.GroupScheme.CoalgebraUnipotence

/-- The finite fixed-vector criterion for exhaustion by reduced right translations. -/
def MatrixUnipotenceConilpotenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (B : Type v) [Ring B] [Bialgebra k B],
    IsMatrixUnipotent k B ↔ IsLocallyConilpotent k B

/-- Reduced-translation exhaustion passes through surjective bialgebra maps. -/
def ConilpotenceQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (B : Type v) [Ring B] [Bialgebra k B]
    (C : Type w) [Ring C] [Bialgebra k C] (q : B →ₐc[k] C),
    Function.Surjective q → IsLocallyConilpotent k B → IsLocallyConilpotent k C

end Langlands.GroupScheme.CoalgebraUnipotence
