# Conditional reduction of regular transfer

`RegularTransferReductionStatement.{u,v}` is an internal implication to the
published `RegularTransferStatement.{u,v}`. It packages the compact-profile
argument used in Henniart–Lemaire (2011), I.2.7, Lemma 2, and I.2.8.
`regularTransferReduction` proves the implication for the original two
universe parameters.

## Premises

- `RegularTransferProfileExistenceStatement` supplies one choice of
  centralizer Haar measures and compatible quotient measures over each
  regular locus. It supplies continuous open orbit parameter maps into
  `Fin n → F` and says the parameters agree across the two sides exactly
  at norm-associated pairs. It requires the chosen centralizer measures
  to be associated at those pairs. On each side the regular locus is
  open and preserved by the relevant conjugation action, which also
  preserves its parameter map. The actual orbital integrals of each
  regular-supported test are integrable, locally constant and constant on
  parameter fibers for those chosen measures.
- `RegularTransferCommutativeCentralizersStatement` supplies commutativity
  of the centralizer of each ordinary regular semisimple element after
  scalar extension to a commutative algebra.

## Proof

The ordinary local-field topology and the finite cyclic algebra topology
give the requisite group topology and continuity of the twist. The
scalar-extension map on each ordinary centralizer is a closed embedding
and hence a measurable embedding. Measure comparison turns an equality
of the chosen orbital integrals at an associated pair into concordance
for all choices at that pair.

For transfer to the ordinary side, descend the given test to its compact
locally constant profile. Every twisted regular element has an ordinary
regular associate, so the profile support lies in the ordinary parameter
image. Realize the profile by an ordinary regularly supported test. A
regular non-norm has parameter outside the twisted parameter image, so
its chosen orbital integral is zero. Inverse rescaling gives zero for
all compatible choices. At an associated pair the two integrals are the
same profile value.

For transfer to the twisted side, descend the ordinary test to its
compact profile. The ordinary vanishing assumption forces its support
to lie in the twisted parameter image. Realize that profile by a twisted
regularly supported test. The ordinary vanishing assumption gives the
off-norm clause, and the common profile once again gives equality at
associated pairs.

The geometric and analytic premises are explicit Lean propositions.
The implication provides a route to the full transfer theorem once
they are proved.
