# Uniqueness of supercuspidal support

Author: Worker 55.

`Langlands.glSupercuspidalSupportUniqueness` proves exactly the published
`Langlands.GLSupercuspidalSupportUniquenessStatement.{uV,uF}`. For every
prime, actual p-adic field, compatible topological data and positive rank,
any two supercuspidal-support multisets of an irreducible smooth complex
representation are equal. The factor-carrier universe `uV` and field
universe `uF` remain independent; the represented object has carrier in
`Type (max uF uV)`. No additional hypothesis is imposed on that object.

The proof combines three published results:

- `CuspidalSupport.glCuspidalTensor` makes each external smooth tensor of
  supercuspidal block factors irreducible and Levi cuspidal.
- `CuspidalSupport.cuspidalInductionReverseAssociation` associates two
  irreducible cuspidal inducing representations whose canonical normalized
  inductions have a common actual irreducible subquotient.
- `CuspidalSupport.glCuspidalTensorAssociation` identifies the multisets of
  cuspidal data represented by associated external tensors.

Unpacking the two support relations supplies ordered families of cuspidal
data, rank-sum equalities, actual supercuspidal representatives, and actual
subquotient presentations of the given representation in their product
inductions. The first result supplies irreducibility and Levi cuspidality
of both external tensors. The product-induction objects in the support
relation are definitionally the canonical normalized Levi inductions used
by the reverse association theorem, with the same upper-parabolic
normalization and factor order.

Write the two subquotient isomorphisms as `e` and `e'`, from the given
representation to the respective subquotients. Irreducibility transfers
along `e`, and `e.symm.trans e'` identifies the two actual subquotients.
These witnesses give the common irreducible subquotient required by reverse
association. Applying tensor association then equates the multisets of
the two ordered families. The enumeration equalities from the original
support witnesses transfer this equality to the requested multisets,
including their ranks, isomorphism classes and multiplicities.

This is internal assembly of the published results and support definitions.
The motivating source for the unchanged target is Zelevinsky 1980,
Proposition 1.10; the implemented route uses the common-subquotient-to-
association direction of Bernstein–Zelevinsky 1977, Theorem 2.9(a), and
tensor-factor association as in Example 2.7. Their provenance is recorded
in the respective unchanged statement pairs. The proof needs only the
reverse association implication and does not assume the other directions
of the full association theorem.

The imported project closure contains foundational segment and
supercuspidal data, tensor algebra, normalized induction, Jacquet
constructions and proofs, geometric-lemma inputs, finite filtrations and
actual subquotient algebra. It contains no derivative module and no
segment classification, head or socle existence, segment product
irreducibility, multisegment exhaustion, quotient coverage, ordered
conversion, tempered uniqueness, or square-integrable/regular
classification or exhaustion proof. In particular the argument does not
use the downstream generic-segment product uniqueness or the two-factor
nonadjacent irreducibility conclusion. A conservative project import scan
and a comment/string-stripped excluded-name scan were performed on the
published inputs and this closing module; these are dependency checks,
not a replacement for independent semantic review.

The existing statement and imported Lean/Markdown pairs are unchanged.
