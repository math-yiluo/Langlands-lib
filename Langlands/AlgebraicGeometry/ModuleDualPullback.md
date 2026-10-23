# Canonical pullback comparison for dual module sheaves

For arbitrary schemes X and Y in a common universe, a scheme morphism
f : X ⟶ Y and a module sheaf M on Y,
`Langlands.Scheme.Modules.dualPullbackComparison f M` constructs

```text
(AlgebraicGeometry.Scheme.Modules.pullback f).obj (dual M) ⟶
  dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).
```

Here `dual` is the internal dual from [ModuleDual](ModuleDual.md), and
`pullback` is Mathlib's scheme-module pullback. The only explicit arguments
are f and M. Pullback of a local module morphism, followed by the canonical
structure-module comparison `pullbackUnitIso f`, gives `localDualPullback`.
Its restriction and scalar laws assemble a module-sheaf morphism
`dualPushforwardComparison f M` from `dual M` to the pushforward of the target
dual. The desired comparison is its mate under
`pullbackPushforwardAdjunction f`.

The proof imports [ModuleLocalHomPullbackProofs](ModuleLocalHomPullbackProofs.md)
for restriction and scalar laws,
[ModuleLocalHomPullbackCoherenceProofs](ModuleLocalHomPullbackCoherenceProofs.md)
for local identity and composition, and
[PullbackUnitProofs](Modules/PullbackUnitProofs.md) for coherence of the
canonical structure-module comparison.

## Local laws and assembly

The zero, addition and naturality lemmas for `localDualPullback` use published
results. The helper `localHomPullback_postcompose` specializes local-Hom
naturality to the identity on the source. Explicit identity equalities avoid
unfolding the restricted module categories in simplification.

`localDualPullback_identity` applies `localHomPullbackIdentity` and the published
`pullbackUnitIdentity`. After identifying the identity inverse-image open with
the given open, the inverse and forward structure-module comparisons cancel.
The remaining precomposition is exactly `dualMap` of the `pullbackId` component.

`localDualPullback_composition` applies local-Hom postcomposition naturality and
`localHomPullbackComposition`. The published `pullbackUnitComposition` identifies
the two successive structure-module comparison maps with the composite
comparison preceded by `pullbackComp`. Its inverse cancels before restricting
the resulting equality to the inverse-image open. This leaves precisely
precomposition by the `pullbackComp` component on the source module, expressed
as `dualMap`.

`localDualPullback_restrict` and `localDualPullback_smul` propagate
`localHomPullback_restrict` and `localHomPullback_smul` from
`ModuleLocalHomPullbackProofs` through the canonical structure-module
comparison. Additivity and scalar compatibility give the linear map on each
open, and restriction compatibility gives its naturality as a presheaf
morphism. This constructs `dualPushforwardComparison`. The lemma
`homEquiv_dualPullbackComparison` identifies the adjoint of the constructed
comparison with this morphism. In particular, `dualPullbackComparison_local`
says that for every open U of Y and h ∈ Γ(dual M, U), evaluation of the
adjoint at h is exactly `localDualPullback f M U h`.

For a : M ⟶ N, `dualPushforwardComparison_naturality` follows sectionwise
from local naturality. The hom-equivalence's naturality in both arguments
then proves `dualPullbackComparison_naturality`:

```text
(pullback f).map (dualMap a) ≫ dualPullbackComparison f M =
  dualPullbackComparison f N ≫ dualMap ((pullback f).map a).
```

## Identity and composition

Global identity and composition coherence are proved for the
mate. `dualPullbackComparison_id` states that the comparison for
`𝟙 X` equals the `pullbackId` component on `dual M` followed by `dualMap` of the
`pullbackId` component on `M`. `dualPullbackComparison_comp` states that the
comparison for `f ≫ g` equals the inverse `pullbackComp` component on `dual M`,
then the pullback along `f` of the comparison for `g`, then the comparison for
`f` at `(pullback g).obj M`, then `dualMap` of the inverse `pullbackComp`
component on `M`.

Both proofs apply the injective hom-equivalence of the relevant adjunction. A
shared `homEquiv_conjugate` helper moves a precomposition by a natural transformation of left
adjoints across hom-equivalences, producing its conjugate transformation. The
published Mathlib conjugates of `(pullbackId X).hom` and `(pullbackComp f g).inv`
are `(pushforwardId X).inv` and `(pushforwardComp f g).hom`, whose components are
identities. For composition, `homEquiv_comp_map` evaluates the hom-equivalence
of the composite adjunction on `(pullback f).map k ≫ l`. After evaluation on a
section over an open, the identity case is `localDualPullback_identity`. The
composition case is `localDualPullback_composition`, followed by cancellation of
the `pullbackComp` components through `dualMap_comp` and `dualMap_id`. Both helpers
are reused from
[PullbackUnitProofs](Modules/PullbackUnitProofs.md).

## Provenance and scope

The registered original is
`stacks-relative-differentials-internal-hom-2026-10-21`, the HTML snapshot of
Stacks Project Section 17.22 ([tag 01CM](https://stacks.math.columbia.edu/tag/01CM)),
opening definition and Lemma 17.22.5
([tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)). The opening interprets
internal-Hom sections as morphisms of restricted module sheaves; the lemma
displays the canonical pullback comparison for internal Hom. The present map
is its derived specialization with target the structure module, followed by
the canonical `pullbackUnitIso f`. Its construction pulls back each restricted
module morphism and then uses the actual pullback-pushforward adjunction to
assemble the global map.

The naturality and identity/composition formulas are derived compatibility
laws for this construction, using Mathlib's actual `pullbackId` and
`pullbackComp`. They are not separate assertions quoted from the source.
All schemes, morphisms and module sheaves are arbitrary; the construction and
laws have no flatness, finite-presentation or local-freeness hypotheses. This
module asserts no base-change isomorphism. The cited lemma's isomorphism
conclusion assumes finite presentation and flatness and is not used here.

## Authorship

Worker 5 authored the local dual laws, global assembly, naturality and source
explanation. Worker 274 authored the global identity/composition proofs and
integrated the local-Hom sheaf-law proofs into the assembly.
