# Uniqueness of real Whittaker coefficient maps from evaluation

`RealWhittakerEvaluationStatement` compares two smooth moderate-growth
Whittaker intertwiners of the same real K-finite standard module. If they
agree at the identity on every source vector, they are equal as
function-valued linear maps.

The proof pulls each coefficient back along the projection from the
archimedean group of a number field to one real matrix factor. The
projection is surjective by assembly of the local matrices. On the
open matrix chart it is a real-linear algebra homomorphism.
The chain rule identifies right derivatives of pulled-back functions
with the pullbacks of their derivatives in the projected directions.
Complex linearity and the universal enveloping algebra extend this
identity to all enveloping operators.

The global enveloping projection is surjective, so it sends central
elements to central elements. The real standard module has an
infinitesimal character, which makes the center orbit of each
pulled-back coefficient finite. Its compact orbit lies in the image of
the finite compact orbit span of its source vector. The Library's
compact differential finiteness and joint finiteness results give
the hypotheses of its real analyticity theorem.

Every archimedean matrix belongs to a connected component meeting the
compact subgroup. At a compact representative, the difference of the
two coefficients and all its enveloping derivatives vanish. Indeed,
each is the difference at the identity evaluated on a compact
translate of an enveloping derivative of the source vector. The
zero-jet and analytic uniqueness theorems propagate vanishing across
the component. Taking the real place of `ℚ` gives the stated local
uniqueness.

This internal result applies to the Library coefficient model used
in Jacquet's principal-series reduction. It allows comparison of
coefficient maps by their scalar evaluations. The bounded
realization and equivariant extension of these evaluations remain
separate proof obligations.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemma 2.4 and §11](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
