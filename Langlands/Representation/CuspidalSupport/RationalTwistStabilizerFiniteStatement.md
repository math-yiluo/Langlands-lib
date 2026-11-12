# Finite unramified twist stabilizers (Renard V.2.7, Lemma): statement

Author: Worker 1222. Module
`Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteStatement`, namespace
`Langlands.CuspidalSupport`. The module contains one **statement**, the closed `Prop`-valued
definition `RationalTwistStabilizerFiniteStatement` (universe parameters `uF, uV`). It proves
nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
**9 July 2026**, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 1222 read
V.2.7, printed pp.108–109 / PDF pp.114–115, for this unit:

> Le groupe des caractères non ramifiés `X(G)` agit sur l'ensemble des classes
> d'équivalences de représentations irréductibles lisses de `G`, `Irr(G)` par
> `(ω, π) ↦ π ⊗ ω`. Le stabilisateur de `π ∈ Irr(G)` est noté `X(G)(π)`, c'est-à-dire
> `X(G)(π) = {ω ∈ X(G) | π ⊗ ω ≃ π}`.
>
> **Lemme.** Soit `π ∈ Irr(G)`. Alors `X(G)(π)` est fini.

The proof restricts to the lift `C_{A_G}` of the finite-index sublattice `Λ(A_G)` of `Λ(G)`
into the split centre, on which `π` acts by a character by Schur's lemma, and uses that only
finitely many characters of `Λ(G)` are trivial on `Λ(A_G)`. Here `G` is (the group of
rational points of) a connected reductive group over a nonarchimedean local field `F`
(V.1–V.2).

## Published objects used

From [RationalInertia](RationalInertia.md) (module
`Langlands.Representation.CuspidalSupport.RationalInertia`), which implements the inertia
relation of V.2.7:

- `unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)`, the published
  group of actual unramified characters of `G(F)`: continuous characters `G(F) → ℂˣ` trivial on
  the common kernel of the norms `|χ|_F` of all rational characters `χ` of `G`. This is
  Renard's `X(G)`.
- `rationalUnramifiedTwist G χ A`, the published twist `A ⊗ χ` of a smooth representation by
  an unramified character, on the same carrier.

The rational points carry the canonical topology `rationalPointTopology F G.X`, with the
published `rationalPoint_isTopologicalGroup`, as in the published VI.4.1 statements of this
directory.

## Lean statement

`RationalTwistStabilizerFiniteStatement` quantifies over a nonarchimedean local field
`F : Type uF` (`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`)
and a group scheme `G` over `Spec F` with `hG : GroupScheme.IsConnectedReductive G`. From
`hG` it installs affineness and smoothness, the canonical topology on `G(F)` and its
topological group structure, exactly as the published
`RationalSummandHomEquivalenceStatement` does. For every smooth complex representation
`A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)` with `A.IsIrreducible`, it asserts
that

```lean
{χ : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) |
  Nonempty (rationalUnramifiedTwist G χ A ≅ A)}.Finite
```

The set is Renard's `X(G)(π)`, with `π ⊗ ω ≃ π` read as an isomorphism of smooth
representations.

## Provenance and departures from the source

The provenance is the source Lemma.

- **`Irr(G)`.** The source's `π` is an equivalence class of irreducible smooth representations;
  the statement quantifies over representatives, and the stabilizer depends only on the class.
  No admissibility is assumed, as in the source.
- **Sizes.** The carrier universe `uV` is independent of `uF`.
- **The Corollary.** The Corollary of V.2.7 (orbits of `X(G)` are complex algebraic tori)
  needs the variety structure of `X(G)` of V.2.4 and is not stated here.

## Scope

This module states the Lemma of V.2.7 and proves it in no part. The published construction
`RationalInertia` records the finite stabilizer as a remaining obligation; this unit supplies
its statement. A proof belongs to a separate proof task.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalInertia` | `unramifiedCharacters`, `rationalNormCharacters`, `rationalUnramifiedTwist`, `rationalPointTopology`, `rationalPoint_isTopologicalGroup`, `SmoothRep` |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
