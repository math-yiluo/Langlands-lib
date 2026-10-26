# Associated-sheaf comparison between finite etale torsors

Author: Worker 558. This module defines a proposition target; it provides no
proof of that proposition.

`Langlands.Shimura.Coefficients.EtaleAssociatedCoverComparisonStatement`
quantifies an actual scheme `X : Scheme.{u}`, groups `G H : Type u`, and actions
`Y : Action X.Etale G` and `Z : Action X.Etale H` on actual objects of the
small etale category of the same scheme. Both `IsFiniteGeometricTorsor X Y`
and `IsFiniteGeometricTorsor X Z` are hypotheses. Each predicate requires a
finite group, a finite surjective etale cover, and unique transport by deck
elements between geometric lifts with the same image in `X`, over every
separably closed field in universe `u`.

The remaining geometric inputs are an arbitrary homomorphism `φ : H →* G`
and an equivariant cover map

```text
a : Z ⟶ (Action.res X.Etale φ).obj Y.
```

For every commutative ring `R : Type u` and representation
`M : Action (ModuleCat.{u} R) G`, write
`M|H = (Action.res (ModuleCat.{u} R) φ).obj M`. The conclusion is

```text
IsIso (etaleCrossCoverMap X φ a (identity on M|H)).
```

This is invertibility of the specific constructed morphism

```text
(etaleAssociatedFunctor X Y).obj M
  ⟶ (etaleAssociatedFunctor X Z).obj M|H
```

in `Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)`.
`IsIso` is Mathlib's categorical assertion that this morphism has a two-sided
inverse. The coefficient morphism is the identity of the restricted
representation, with its actual restricted action. The scheme, both groups,
ring and module carriers share universe `u`; the site's object universe is
the existing one of `X.Etale`.

The imported `EtaleCrossCover` construction first restricts sections along
the product of `a.hom` with the identity, then uses the coefficient morphism
and the universal property of invariant sheaves. Its cover direction is
contravariant: the cover map from `Z` to `Y` induces the displayed sheaf map
from the sheaf associated to `Y` to the sheaf associated to `Z`. The imported
diagonal action in `Associated` combines pullback by the inverse deck
transformation with the coefficient action. This proposition uses that
construction unchanged.

The target is internally derived from these categorical constructions and
local torsor trivialization; it is not a transcription of an external
theorem. Existing Library ingredients explain its proposed proof route.
In the namespace `Langlands.Shimura.Coefficients`,
`etaleTorsorSectionSplitting` from `TorsorSectionSplittingProof` obtains
graph-section splitting from each geometric torsor hypothesis.
`associatedEvaluation_bijective` from `TrivializationFromSplitting` and
`associatedTrivializationAlongOfSplitting` from `CrossCoverEvaluation`
express the resulting invertibility of canonical evaluation at a chosen lift.
After restricting to the localized site over `Z.V`, evaluate the target at
its tautological lift and the source along `a.hom`.
`crossCoverMap_evaluation` identifies the localized comparison followed by
target evaluation with source evaluation, since the coefficient map is the
identity. Both evaluations are isomorphisms by the torsor hypotheses.
Descent of this local invertibility along the surjective etale cover `Z.V`
is the remaining global step of the intended argument. This explanation
is a provenance rationale and proof plan, not a proof supplied by this
statement module.

The statement places no surjectivity assumption on `φ` or `a`. It imposes
no invertibility of group orders in `R`, finiteness of the coefficient
module, or exactness of arbitrary invariants. Its role is to justify
reversing this cover comparison when constructing coefficient inverse
systems with varying torsors. Tensor or reduction compatibility, existence
of Harris level schemes and torsors, and comparisons with cohomology are
separate obligations.

The sole direct import is
`Langlands.Shimura.Coefficients.EtaleCrossCover`, which imports `Etale`.
Formal environment: Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. No imported declaration or
companion Markdown is changed.
