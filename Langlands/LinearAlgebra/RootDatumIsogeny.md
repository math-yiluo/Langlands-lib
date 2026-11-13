# Isogenies of reduced root data

`Langlands.LinearAlgebra.RootDatumIsogeny p P Q` implements Milne's
isogeny of root data, including root-dependent powers of the characteristic
exponent. Its weight map goes from the weight lattice of `P` to that of `Q`;
its coweight map goes in the opposite direction.

The parameters include finite root indexing types, finitely generated weight
and coweight lattices over `ℤ`, and reducedness of both root data. Mathlib's
`RootDatum` supplies a perfect integral pairing. Finite perfectly paired
integral lattices are free. Neither roots nor coroots are required to span the
whole lattice, so reductive data with a central torus are included.

## Original source and conventions

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), Definition 23.1, Definition 23.2 and
Example 23.3, printed pp.483–484, one-based PDF pp.499–500. It is registered
as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete official errata snapshot, registered as
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no correction to these definitions or example.

Milne writes an isogeny as `f : X' → X` and indexes its factor by a root
`α` in the receiving root datum. Here `P` corresponds to his primed datum,
`Q` to his unprimed datum, and `indexEquiv i` is the receiving root
corresponding to the source root `i`. Thus `rootFactor i` is his
`q(α)` for `α = Q.root (indexEquiv i)`. The two equations are exactly

```
weightMap (P.root i) = rootFactor i • Q.root (indexEquiv i)
coweightMap (Q.coroot (indexEquiv i)) = rootFactor i • P.coroot i
```

The natural factor acts through its image in `ℤ`. Each factor is a power
`p ^ n`, with `n : ℕ`. The field-independent parameter `p` is required to
be one or prime. When used over a field, it must be identified with that
field's characteristic exponent by the consumer.

Definition 23.1 requires the weight map to be injective with finite cokernel.
Immediately after it, on printed p.484, Milne gives the equivalent condition
that the weight map and its dual are both injective. The structure uses this
second formulation and explicitly includes all finite-lattice hypotheses.
The transpose equation identifies the supplied coweight map with the dual
map under the perfect pairings. A separate finite-cokernel theorem is not
provided in this module.

This is Milne's isogeny notion. As his notes on p.484 explain, the more
general SGA 3 notion of a p-morphism need not be an isomorphism after
tensoring with `ℚ`; that broader notion is not defined here.

## Implemented constructions

`IsCentral` means every root factor is one, as in Definition 23.2.
`ofHom` takes an existing `RootPairing.Hom` and proofs that both its lattice
maps are injective; it sets every factor to one. Conversely, `toHom` takes
a central isogeny and recovers an exact root-preserving `RootPairing.Hom`
with the same lattice maps and root correspondence. `isCentral_one`
proves that characteristic exponent one forces centrality. Positivity of
the exponent and every root factor follows from the stored power condition.

`id` uses the identity exact morphism. `comp g f` composes weight maps,
composes coweight maps in the reverse direction, and uses the root factor
`f.rootFactor i * g.rootFactor (f.indexEquiv i)`. Transposition follows
by evaluating the two transpose equations; the scaled root and coroot
equations follow by linearity. The product is a power of `p` by addition
of the two power exponents.

`frobenius hp P n` implements Example 23.3: both lattice maps multiply by
`p ^ n`, the root correspondence is the identity, and every root factor
is `p ^ n`. Perfectness implies torsion freeness, so multiplication by
this positive integer is injective. The transpose equation follows from
bilinearity.

These adapters and composition are direct constructions from the source
definition. The module does not assert existence of a realizing group-scheme
isogeny or uniqueness of such a realization. In particular the Frobenius
construction here is a root-datum map; it does not identify a group scheme
with its Frobenius twist.
