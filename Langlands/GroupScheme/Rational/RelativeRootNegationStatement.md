# Negation stability of the actual relative roots

Author: Worker 1269.

`Langlands.GroupScheme.RelativeRootNegationStatement` is an unproved
proposition target. For every field `k : Type u`, connected reductive group
scheme `G` over `Spec k`, and maximal split torus inclusion
`i : T.toGrp ⟶ G`, it asserts

`∀ α ∈ relativeRoots i, -α ∈ relativeRoots i`.

The roots are the published actual Lie weights: nonzero characters of `T`
whose adjoint weight space in `Lie(G)` is nonzero. Negation is the additive
inverse in the published character lattice. There is no root-system premise.
The field may be imperfect and of any characteristic; the group need not be
split, and its relative-root system may be nonreduced. The statement also
includes the empty root set.

## Source and derived provenance

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§2.6(b), printed p.93 (PDF p.124), states that the relative roots of a
maximal split torus of a connected reductive group over an arbitrary field
form a root system. The arbitrary-field convention is explicit at the
start of §2.6, printed p.92 (PDF p.123). Negation stability is a derived
consequence of that assertion, for the source's potentially nonreduced
relative-root system.

The registered *Corrections and Additions* (2024), source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.25, lists Section 2.6 corrections. None changes this root-system
assertion or its arbitrary-field scope.

This is a focused structural target for consumers that need to pass from a
negative relative root to its positive opposite. It does not define another
root system or prove the existing `RelativeRootSystemStatement`; that
larger target retains its separate proof obligation. The present module
defines the proposition and supplies no proof of negation stability.
