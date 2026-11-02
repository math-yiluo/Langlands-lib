import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Split

/-! # Split tori are reductive: statements -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.IsSplitTorus

/-- Milne, Corollary 19.18: over every field `k`, a split torus is a connected reductive group. -/
def IsConnectedReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus G → IsConnectedReductive G

/-- Over every scheme `S`, a split torus is a reductive group scheme in the sense of Conrad,
Definition 3.1.1. -/
def IsReductiveStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsSplitTorus G → IsReductive G

/-- Both statements of this module together. -/
def ReductiveStatement : Prop :=
  IsConnectedReductiveStatement.{u} ∧ IsReductiveStatement.{u}

end Langlands.GroupScheme.IsSplitTorus
