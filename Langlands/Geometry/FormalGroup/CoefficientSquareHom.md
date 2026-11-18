# Actual formal Hom along a commutative coefficient square

This is internal coefficient infrastructure for the formal module constructions,
derived from the published coefficient extension, identity-coordinate comparisons
and tensor Hom definitions. It attributes no numbered theorem to the literature.

Let `O` be a commutative ring, and let `R`, `S`, `A` and `B` be commutative
`O`-algebras. Consider actual `O`-algebra maps

```text
R --α--> A
|        |
φ        β
|        |
v        v
S --δ--> B
```

with the supplied equality `β.comp α = δ.comp φ`. The coefficient rings can
occupy different universes. The formal modules have finite coordinate types,
which need not agree.

`Hom.mapSquareLinear` sends an actual integral formal module map over `A` to
an actual map between the two modules obtained by extension first to `S` and
then to `B`. It extends the map through `β` and transports its source and target
through the existing `mapSquareIso` identity-coordinate comparisons. In
particular, it uses actual maps and an actual commutative square, rather than
assuming a transport operation. Its coordinate series are exactly the original
series with coefficients mapped through `β`.

The construction is `O`-linear. Its identity and composition laws follow by
equality of the coordinate series and the corresponding coefficient extension
laws. If the input is the extension of a map over `R`, its output is the
successive extension along `φ` and `δ`; this follows from the supplied
commutativity equality.

For any `O`-algebra field `F`, `RationalHom.mapSquareLinear` is obtained by
tensoring this integral linear map with `F`. Its formula on a pure tensor
preserves the `F` coefficient. Tensor induction proves that it preserves
identities and the existing bilinear composition, and that it agrees with
successive extension on rational maps from `R`.

No fraction-field, domain, nilpotence, finite-kernel or isogeny hypothesis is
required. This unit constructs maps between actual integral Hom and tensor Hom;
the pullback of arbitrary sheaf sections is a further construction.
