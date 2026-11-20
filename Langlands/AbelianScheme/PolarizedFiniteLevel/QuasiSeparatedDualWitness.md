# Dual witnesses over quasi-separated bases

## Declaration

`Langlands.AbelianScheme.PolarizedFiniteLevel.DualWitness.ofQuasiSeparated A`: for an
abelian scheme `A` over a scheme `S` with `QuasiSeparatedSpace S`, a `DualWitness A`
with:

- `hasDual`: the Library's proof `relativeDualSchemeExistence S A` (existence of the
  universal Picard-zero family over quasi-separated bases);
- `geometry`: `relativeDualSchemeGeometry S A _` (the chosen dual parameter scheme is
  smooth, proper and geometrically connected);
- `inverseBundle`: the chosen tensor inverse `LineBundle.inverse` of the Poincaré line
  bundle (the underlying line bundle of `poincareFamily A _`);
- `evaluation`: `LineBundle.tensorInverseIso` of that line bundle.

The line bundle is passed explicitly to `tensorInverseIso`; leaving it to unification
times out.

## Use

Every level base is locally noetherian, hence quasi-separated (Mathlib instance
`IsLocallyNoetherian.quasiSeparatedSpace`). So any abelian scheme over a level base, in
particular an abelian scheme glued from local pieces, has a dual witness without gluing
dual schemes.

## Provenance

Internal: assembles proved Library results.
