# Inner cuspidal support for an upper Jacquet module

Author: Worker 125.

This internal adapter changes upper refined Jacquet coordinates to opposite
coordinates by reversing the fine blocks inside each coarse block. Its maps
are the published actual quotient equivalences, including normalization.
The field and representation carriers have independent universes. The reversal
maps and their cuspidality property do not require positive ambient rank,
smoothness, or irreducibility. The two conditional support adapters assume
positive rank, irreducibility and Levi cuspidality of the fine input and output,
an actual surjection from the specified inner induction, and an actual upper
Jacquet subquotient. They do not require the quotient representation itself to
be irreducible.

The first lemma extends the published componentwise minimality criterion
from equal refinements to possibly different refinements: the increasing
conditions and their inverse conditions are checked independently on the
source and target flattened blocks. The double-reversal identities use
`GeometricExcessBranch.reverse_reverse` and its assembled permutation identity.
The inverse reversal is minimal, since each component is the inverse
reversal representative supplied by
`OppositeCuspidalJacquetFiltration.isMinimalRepresentative_reverse_inv_mul`
at the identity.

`flattenedUpperToOppositeReverseEquiv` specializes
`Geometric.RefinedOppositePieceTransport.flattenedNormalizedOppositeReverseEquiv`
to the reversed refinement. A local conversion eliminates the equalities of
the double-reversed refinement with the original refinement and of the second
permutation with the inverse first permutation. This handles the dependency of
the Levi conjugacy proof and the actual coinvariant carrier on the refinement.
The result identifies the upper quotient transported by inverse inner reversal
with the opposite quotient at the reversed refinement. Cuspidality under this
transport uses published admissibility under continuous Levi conjugation and
quasicuspidality under minimal Levi transport.

`exists_transport_of_upper_quotient_of_constituent` restricts the given actual
upper subquotient along inverse inner Levi conjugation. The reversal equivalence
makes the transported output an actual opposite subquotient at the reversed
refinement; irreducibility and cuspidality survive this transport. The earlier
`InnerCuspidalQuotientSupport.exists_transport_of_quotient_of_constituent`
then supplies a coarse block Weyl element `h`, conditional on the existing
`GLCuspidalInductionJacquetConstituentStatement`. That earlier adapter descends
the actual surjection to opposite Jacquet quotients and applies the stated
constituent premise. Transport back by the inner reversal `r` cancels its inverse
on the output and composes the source permutation to `r * h`. Both `r` and `h`
belong to `blockWeyl B`, so their product does too. The resulting equivalence
identifies the original output with transport of the original fine input.

`exists_transport_fineTwist_of_upper_quotient_of_constituent` uses the same
argument on the determinant twist of the fine input by `-v`. Published real-twist
invariance supplies its irreducibility and Levi cuspidality. Unfolding
`RelativeJacquetMultiplicity.fineTwist` at coarse parameter zero gives exactly
this input in refined coordinates. There is no restriction on the real fine
parameter `v`.

The provenance is internal composition of the named Library constructions and
the earlier quotient-map adapter. No geometric lemma, cuspidal-induction
constituent statement, or persistence statement is proved here. The constituent
premise remains an explicit separate proof obligation in both support adapters.
