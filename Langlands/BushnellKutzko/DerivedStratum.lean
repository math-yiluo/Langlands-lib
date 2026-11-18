import Langlands.BushnellKutzko.PureSimpleStratum
import Langlands.BushnellKutzko.TameCorestriction

/-! # Refinements and derived strata (BK93 §2.2, printed p. 51) -/

namespace Langlands.BushnellKutzko

universe uO uK uE uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

namespace Stratum

/-- A refinement `[𝔄,n,r−1,β+b]` of a simple stratum `[𝔄,n,r,β]`,
with `b ∈ 𝔓^{−r}` (BK93 p. 51). -/
def IsRefinement (S T : Stratum O K V) : Prop :=
  S.IsSimple ∧ T.chain.order = S.chain.order ∧ T.n = S.n ∧ T.r = S.r - 1 ∧
    T.b - S.b ∈ S.chain.endFiltration (-S.r)

variable (E : Type uE) [Field E] [Algebra K E] [Module E V] [IsScalarTower K E V]

/-- The field action `E → End_K(V)` identifies `E` with `K[S.b]`. -/
def IsGeneratedField (S : Stratum O K V) : Prop :=
  ∃ β : E, subfieldEmbedding K E V β = S.b ∧ Algebra.adjoin K ({β} : Set E) = ⊤

variable [Algebra O E] [IsScalarTower O K E]

/-- `D` is the derived stratum `[𝔅,r,r−1,s(b)]` over `E`, for the
simple stratum `S` and the perturbation `b ∈ 𝔓^{−r}` (BK93 p. 51).
Its chain uses exactly the lattices of the original chain, now over the integral closure. -/
def IsDerivedStratum (S : Stratum O K V) (b : Module.End K V)
    (s : TameCorestriction O K E V)
    (D : Stratum (integralClosure O E) E V) : Prop :=
  S.IsSimple ∧ S.IsGeneratedField E ∧ b ∈ S.chain.endFiltration (-S.r) ∧
    (∀ i : ℤ, (D.chain.lattice i : Set V) = (S.chain.lattice i : Set V)) ∧
    D.n = S.r ∧ D.r = S.r - 1 ∧ D.b = s b

/-- The derived stratum exists and is equivalent to a simple stratum in
`End_E(V)`, with exactly the same order and integer parameters.
This is internal notation for the conclusion used in BK93 (2.4.1)(iii), (2.4.2)(vi). -/
def DerivedEquivalentToSimple (S : Stratum O K V) (b : Module.End K V)
    (s : TameCorestriction O K E V) : Prop :=
  ∃ D C : Stratum (integralClosure O E) E V,
    S.IsDerivedStratum E b s D ∧ C.chain = D.chain ∧ C.n = D.n ∧ C.r = D.r ∧
      D.Equivalent C ∧ C.IsSimple

end Stratum

end Langlands.BushnellKutzko
