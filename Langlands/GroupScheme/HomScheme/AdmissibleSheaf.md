# Sheafness from effective admissible descent

Author: Worker 1726.

This internal module reduces unique gluing of the small and total presheaves of
actual closed torus subgroups to effective admissibility of the explicit
`matchingSubgroup`. The premise `HasEffectiveAdmissibleDescent` retains exactly
that obligation for all parameter schemes and open covers.

Compatible small presheaf sections decode to actual families satisfying
`IsMatchingAdmissible`. Their matching subgroup gives a glued admissible
section under the effective-admissibility premise. Its local recovery proves
existence of an amalgamation, and equality detected on cover restrictions
proves uniqueness.

For the total presheaf, first glue the structural maps to the original base
using actual scheme morphism gluing. Move the local total sections into the
fibres over these glued structural maps. Naturality of the total-to-fibre
operation transfers compatibility to the relative presheaf. Relative gluing
then gives a total section, and the inverse fibre identities verify its local
restrictions and uniqueness. This part is proved for an arbitrary presheaf on
the slice before it is specialized to actual admissible families, so it uses
only the total-presheaf identities.

Finally, `totalAdmissible_isSheaf` proves the full sheaf condition for
`Scheme.zariskiTopology`. Every covering sieve contains a small open cover.
The cover gluing theorem gives sheafness for its generated sieve; after any
pullback, the pulled-back open cover detects equality. The subsieve sheaf
criterion then gives sheafness for the original covering sieve. All parameter
schemes and test schemes remain arbitrary in universe `u`.

The constructions and proofs are internal consequences of the actual family
restriction and total-presheaf interfaces. The effective-admissibility premise
is explicit and remains to be proved separately.

The parameter-slice cover reuses `Langlands.AlgebraicGeometry.Picard.openCoverOver`; its objects and arrows are the same actual cover objects and maps used by the admissible-family interface.
