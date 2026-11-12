# Reduction of the cubic direct-image theorem to algebraically closed fibres

`CubicDirectImageReductionStatement` is an internal reduction between two
existing published theorem targets in this directory:

- `CubicFibreCohomologyStatement`: for every published `Prerequisites` `P`,
  every algebraically closed field `K`, all `g d n` with `0 < d`, and every
  datum `a : Datum P (Spec K) g d n`, the actual cubic diagonal bundle
  `a.cubicBundle` has vanishing `relativeCohomology` in every positive degree,
  and its degree-zero cohomology has `K`-dimension `6^g*d`;
- `CubicDirectImageStatement`: for every `P`, every locally noetherian base
  `S`, all `g d n` with `0 < d`, and every datum `a : Datum P S g d n`, the
  module `a.rigidificationModule` is locally free of rank `6^g*d`
  (`IsLocallyFreeOfRank`), and `a.rigidificationBaseChangeMap b` is an
  isomorphism for every scheme morphism `b : S' ⟶ S`.

The proposition is the implication
`CubicFibreCohomologyStatement.{u} → CubicDirectImageStatement.{u}`, in one
fixed universe `u`. Both sides are used exactly as published; this module adds
no hypothesis to either side and changes neither definition. In particular the
conclusion keeps the actual direct image `a.rigidificationModule` and the
specified comparison `a.rigidificationBaseChangeMap b`, with an arbitrary
changed base `S'`.

## Provenance

This is an internal statement. It isolates the cohomology-and-base-change part
of the direct-image theorem from its geometric-fibre input, so that the two
can be proved and reviewed separately. The fibre input is the separate target
`CubicFibreCohomologyStatement`; the sources of both sides are recorded in
their own Markdown files (Mumford, Fogarty and Kirwan, *Geometric Invariant
Theory*, third edition, Definition 7.5 and its footnote, printed page 130,
and Proposition 6.13, printed pages 123–124). In the source the implication
is the standard step that a proper flat family whose fibres have cohomology
only in degree zero, of constant dimension `r`, has a locally free direct image
of rank `r` commuting with every base change.

This module states the reduction and does not prove it. Proving it does not
prove either `CubicFibreCohomologyStatement` or `CubicDirectImageStatement`.
