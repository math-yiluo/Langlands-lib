import Langlands.GroupScheme.Reductive.Basic

/-! # `GL_n` is reductive: statements -/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- Milne, Example 19.19: over every field `k`, the general linear group scheme `GL_n` is a
connected reductive group. -/
def IsConnectedReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n],
    IsConnectedReductive (groupScheme n (CommRingCat.of k))

/-- Over every commutative ring `R`, the general linear group scheme `GL_n` over `Spec R` is a
reductive group scheme in the sense of Conrad, Definition 3.1.1. -/
def IsReductiveStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}),
    IsReductive (groupScheme n R)

/-- Both statements of this module together. -/
def ReductiveStatement : Prop :=
  IsConnectedReductiveStatement.{u} ∧ IsReductiveStatement.{u}

end Langlands.GroupScheme.GeneralLinear
