# The general isogeny theorem for split reductive groups

This module declares the two forms of Milne Theorem 23.9 for connected
reductive group schemes over arbitrary fields. The declarations return
`Prop`; they are proof targets, and this module does not prove them.

`Langlands.GroupScheme.SplitIsogenyExistenceStatement` asserts that every
isogeny

```
f : RootDatumIsogeny (ringExpChar k) P' P
```

between the root data of specified split maximal tori `T ⊆ G` and
`T' ⊆ G'` arises from an actual isogeny `φ : G → G'` and an isogeny
`t : T → T'`. Their square with the torus inclusions commutes, and
their lattice maps agree with the given data:

```
f.weightMap χ = t ≫ χ
f.coweightMap ν = ν ≫ t.
```

`Langlands.GroupScheme.SplitIsogenyExtensionStatement` states the
criterion for a fixed actual isogeny `t : T → T'`. There exists an
isogeny `φ : G → G'` extending `t` exactly when there exists a
root-datum isogeny `f` with these two actual lattice maps.

`Langlands.GroupScheme.SplitIsogenyTheoremStatement` is the conjunction
of these realization and extension assertions.

## Hypotheses and conventions

The ambient groups use the existing `Grp (Over (Spec k))` architecture
and are connected reductive in the geometric sense. Both tori are split
and maximal. The root data are on their actual character and cocharacter
lattices and satisfy `IsRootDatumOf` for the given inclusions. Their root
indexing types are finite and both data are reduced, as required in
Milne §23.a. Finite generation of all four integral lattices follows
from splitness through the published character and cocharacter finiteness
theorems. Central torus directions are allowed.

The exponent is exactly `ringExpChar k`: one in characteristic zero,
and the prime characteristic in positive characteristic. The
`RootDatumIsogeny` input permits nontrivial root-dependent powers of
this exponent in both root and coroot equations. Its lattice maps are
injective and mutually transposed. These statements include general
inseparable isogenies; the input is not restricted to the exact
root-preserving `RootPairing.Hom` of the central case.

`IsIsogeny` means that the underlying scheme morphism is finite, flat
and surjective. No smoothness or reducedness of its kernel is required.
The torus and group maps are actual morphisms of group schemes,
including their actions on nonreduced tests. No assertion identifies
their rational points with a quotient of rational-point groups.

## Original sources and related interfaces

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (2017), Theorem 23.9, printed p.487
(one-based PDF p.503), with Definitions 23.1–23.2, printed pp.483–484
(PDF pp.499–500), and Proposition 23.5, printed pp.485–486
(PDF pp.501–502). The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete retained official errata snapshot,
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no correction to these definitions or assertions.

Milne describes the induced character map; its dual is the actual
cocharacter map by the perfect torus pairing. Specifying both maps
records that comparison explicitly, with directions `X(T') → X(T)`
and `Y(T) → Y(T')`. The root factor indexed by a root of `P'`
corresponds to Milne's factor at its receiving root of `P`.

The existing `SplitCentralIsogenyExistenceStatement` treats central
isogenies using exact `RootPairing.Hom`. The present input permits the
general characteristic-power factors and asks for an `IsIsogeny`
realization. The separate `IsogenyRootDatumStatement` gives the induced
root-datum map and its centrality and isomorphism comparisons.
These statements impose no choice of pinning and make no uniqueness
claim about the realizing group isogeny.
