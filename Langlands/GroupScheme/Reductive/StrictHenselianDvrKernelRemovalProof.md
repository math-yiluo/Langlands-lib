# Closed-fibre kernel removal over a strictly Henselian DVR

`Langlands.GroupScheme.strictHenselianDvrKernelRemoval.{u}` proves the exact
published `StrictHenselianDvrKernelRemovalStatement.{u}` for every universe
`u`, with no additional hypotheses.

The proof supplies the general Henselian finite-part existence proposition
to `strictHenselianDvrKernelRemoval_of_henselianFinitePart`. For each
Henselian local ring and separated, quasi-compact, locally finite-type,
locally quasi-finite morphism to its spectrum, the actual subtype
`Langlands.AlgebraicGeometry.HenselianFinitePart.finitePart f` provides an
open and closed finite part containing the whole closed fibre. Its value
and property give the required existential witness.

The conditional theorem then constructs the finite normal kernel subgroup,
the reductive quotient and the specified factorization. Its conclusions
are that the quotient projection is an isogeny, the remaining map is an
isogeny on every residue-field fibre, and the base change of that particular
remaining map along `Spec.algebraMap R (IsLocalRing.ResidueField R)` is an
isomorphism. The present proof discharges its only extra premise using the
finite-part construction. The target statement and its import closure are
unchanged.

This proof is a derived composition of the named constructions. It uses
their implemented finite-part and quotient arguments and asserts no
additional comparison with the literature.
