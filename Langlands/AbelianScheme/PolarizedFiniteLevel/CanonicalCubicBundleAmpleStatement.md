# Ampleness of the canonical diagonal bundle and its cube over a field

`Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleStatement`
is a proposition definition, with universe parameter `u`. For every published
`Prerequisites P`, every field `K : Type u`, all natural indices `g`, `d`, `n`,
and every actual ordinary polarized datum `a : Datum P (Spec K) g d n`, it
asserts both `a.canonicalBundle.IsAmple` and `a.cubicBundle.IsAmple`.

The first bundle is the actual diagonal Poincaré bundle for the datum's
polarization and its supplied dual witness. The second is its actual third
tensor power. Both conclusions use the published absolute ampleness predicate
on line bundles. No algebraic closure, positivity of `d`, restriction on `n`,
chosen presentation over `K`, or additional ampleness hypothesis is required.

## Internal provenance

This statement packages an internal consequence of published results for the
ampleness step of `CubicFibreCohomologyStatement`. It translates no additional
external theorem.

Take an algebraic closure `F` of `K`, with its canonical map `b : Spec F → Spec K`.
The datum's relative polarization predicate supplies
`HasFieldAmpleMumfordPresentation` for the canonically changed abelian scheme,
dual and polarization over `F`. The published
`poincareDiagonal_isAmple_after_fieldExtension` from
`AmpleMumfordDiagonalProof` makes the pullback of that specified diagonal
bundle ample over a further extension of `F`. The published
`fieldBaseChangeAmpleReflection` reflects this to the same bundle over `F`.
The actual `poincareDiagonalBaseChangeIso` identifies it with the pullback of
`a.canonicalBundle` along the projection over `b`. A second application of
reflection gives ampleness of `a.canonicalBundle` over `K`. Finally the
published `Datum.cubicBundle_isAmple_of_canonicalBundle` gives ampleness of
its actual cube.

Only the existing relative polarization field of the datum is used to choose
the geometric presentation. The dimension, degree and level fields need no
extra conditions for this consequence. The proposition therefore applies over
all fields, including the algebraically closed fields of the host theorem.

This module supplies the statement target. Higher cohomology vanishing,
the degree of multiplication by six, the Euler-square identity and the final
dimension formula remain separate obligations.
