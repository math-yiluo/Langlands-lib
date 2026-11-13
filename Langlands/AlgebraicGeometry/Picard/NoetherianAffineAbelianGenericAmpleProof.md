# Proof: generic ampleness on abelian schemes over noetherian affine domains

`Langlands.AlgebraicGeometry.Picard.noetherianAffineAbelianGenericAmple`
proves the published statement
`Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleStatement.{u}`
for an arbitrary universe `u`. For every noetherian integral domain `R`, every
actual abelian scheme `A` over `Spec R` and every specified line bundle `L` on
`A.X.left`, ampleness of the pullback of `L` along the first projection of the
actual fibre product of `A.X.hom` with
`Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))` implies that
`L` is ample. No hypothesis is added.

## Implemented argument

The theorem applies the reduction
`noetherianAffineAbelianGenericAmple_of_closedLocus` of the module
`Langlands.AlgebraicGeometry.Picard.GenericAmpleFromClosedLocus`
(constructed by Worker 833 and included in this contribution) to two published
proofs:

- `abelianFibreAmpleLocusClosed`, the exact proof of
  `AbelianFibreAmpleLocusClosedStatement`: on an abelian scheme over a locally
  noetherian base, the set of base points whose residue-field fibre carries an
  ample pullback of `L` is closed;
- `properAffineFibrewiseAmple`, the exact proof of
  `ProperAffineFibrewiseAmpleStatement`: on a proper family over a locally
  noetherian affine base, a line bundle that is ample on every residue-field
  fibre is ample.

Inside the reduction, `LineBundle.isAmple_fibre_of_fieldPoint` passes from
the fraction-field pullback to the residue-field fibre at the image point `s`
of the canonical fraction-field point. The field point factors through the
spectrum of the residue field of `s`; pasting the two pullback squares
identifies the fraction-field base change with a base change of the
residue-field fibre along a field extension, ampleness is transported along
that isomorphism, and the published `fieldBaseChangeAmpleReflection` reflects
it to the residue-field fibre. `fractionFieldPoint_asIdeal` shows that `s` is
the zero prime, because the algebra map into the fraction field is injective,
so the closure of `{s}` is all of `Spec R`. The closed ample-fibre locus
contains `s`, hence every point, and the fibrewise criterion over the
noetherian affine base `Spec R` (an abelian scheme is proper) gives ampleness
of `L`.

## Provenance

The statement is the integral affine generic-point consequence of
Faltings–Chai, *Degeneration of Abelian Varieties* (1990), Chapter I,
Remark 1.10(b), printed p. 7, and Theorem 1.9(b), printed p. 6. The Lean
proof follows the route described above rather than the source's argument
through nondegeneracy, Riemann–Roch and semicontinuity, which is contained in
the closedness input.
