# Proof: point surjectivity for z-extensions

This module proves the Library statement
`Langlands.GroupScheme.ZExtensionPointSurjectivityStatement` at an arbitrary
universe `u`:

```text
theorem zExtensionPointSurjectivity : ZExtensionPointSurjectivityStatement.{u}
```

The statement is

```text
∀ (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) (z : ZExtension G),
    Function.Surjective (z.H.affinePointsTarget z.p (CommAlgCat.of k K)).
```

In words: for every field `k`, every field extension `K/k` and every
z-extension `1 → Z → H → G → 1` of a group scheme `G` over `k`, every
`K`-point of `G` lifts to a `K`-point of `H` along `p`. There is no
restriction on `k` or `K`: any characteristic, `k` not necessarily perfect,
and `K/k` not necessarily algebraic, separable or finite. The proof adds no
hypothesis.

## Implemented proof

The proof is a single term with two published Library inputs:

1. `inducedTorusQuotientPointSurjectivity :
   InducedTorusQuotientPointSurjectivityStatement.{u}`, from
   `Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof`. It
   says that an fppf quotient `p : H → G` whose kernel is the image of a closed
   central induced torus `i : Z → H`, with `H` and `G` connected reductive,
   is surjective on `K`-points for every field extension `K/k`.
2. `zExtensionPointSurjectivity_of_inducedTorusQuotient :
   InducedTorusQuotientPointSurjectivityStatement.{u} →
   ZExtensionPointSurjectivityStatement.{u}`, from the statement module
   `Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityStatement`.
   It applies the general statement to `z.Z`, `z.H`, `G`, `z.i` and `z.p`,
   with the fields `induced`, `closed`, `central`, `source_reductive`,
   `target_reductive` and `quotient` of `z.isZExtension`.

The theorem is the second result applied to the first. The only import is the
proof module of item 1, which imports the statement module.

## How the general theorem is proved

This summary describes the published proof of item 1, for orientation; that
proof is not part of this module. The induced torus `Z` is isomorphic to the
Weil restriction of `Gm` from a finite product `B` of intermediate fields of a
Galois splitting field (`inducedTorusWeilDecomposition`), so its points on a
test algebra `T` are `(B ⊗_k T)ˣ`. A `K`-point `g` of `G` lifts to an
`L`-point of `H` for some field extension `L/K`, because the underlying
morphism of `p` is surjective. For two maps out of `L` that agree on `K`, the
quotient of the two restrictions of this lift lies in the kernel of `p`,
hence comes from a unit of `B ⊗_k T`; these units form a descent cocycle.
Because `K ⊗_k B` is semilocal, the cocycle is a coboundary (Hilbert 90 for
a semilocal ring). Correcting the lift by this coboundary gives a point that
descends to a `K`-point of `H` over `g`, by fpqc descent along
`Spec L → Spec K`. Centrality, reductivity, flatness and finite presentation
are not used.

## Provenance

The provenance is derived, as recorded in the statement's Markdown. Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §11.5, printed p. 429
(PDF p. 460), asserts that `G̃(K) → G(K)` is surjective for a z-extension
over the maximal unramified extension `K`. The statement proved here extends
this to every field `k` and every field extension `K/k`. The cohomological
background (Shapiro's lemma and Hilbert 90 for induced tori) is cited in the
Markdown of the statement module.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
