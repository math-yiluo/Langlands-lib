# Norm-one twists on the actual unitary supercuspidal lattice

This derived construction restricts the published scalar-twist equivalences to
the genuine unitary supercuspidal basis. A field with a topology and a complex
representation-carrier universe are independent parameters. At every positive
general-linear group rank, the supplied character has open kernel, is trivial
on the determinant kernel, and has complex norm one at every group element.
No finite-dimensionality, topology, norm, or completeness is imposed on the
representation carrier. Degree means group rank.

`GeneralLinear.SupercuspidalClass.isUnitarizable_twist_iff` reduces along the
actual isomorphism-class quotient to the published
`Langlands.isUnitarizable_twist_iff`. That theorem retains an actual invariant
positive definite Hermitian form under a norm-one scalar twist, and also
transports it back. Thus the class-level statement preserves and reflects
existence of such a form; it does not assume every supercuspidal class unitary.

`Supercuspidal.unitaryTwistBasisEquiv` restricts the actual basis equivalence
using that equivalence of predicates. Its value and rank formulas retain the
ambient twist and group rank. Its formula on a unitary supercuspidal object
uses the published object twist with the transported form-existence witness.
The inverse is the inverse-character family, whose kernels are unchanged and
whose values again have norm one.

`Supercuspidal.unitaryTwistLatticeEquiv` extends this bijection by integral
finite-support reindexing. It sends each single coefficient and generator to
the corresponding twisted unitary class, preserves coefficients at matched
indices, and has the specified inverse-character inverse. Inclusion into the
full supercuspidal lattice commutes with twisting. Integral group-rank degree,
the coefficient pairing, and coefficient nonnegativity are preserved.
Identity and composition laws hold for the basis and lattice; the general
composition interface explicitly assumes that the product kernel is open.

The class argument uses quotient induction. The basis restriction uses
`Equiv.subtypeEquiv`, and the lattice extension uses the published `reindex`
operation, implemented by `Finsupp.domLCongr`. The inclusion, degree, and
pairing laws follow by finite-support linear induction; effectiveness uses
surjectivity of the restricted basis equivalence. These are intrinsic
construction proofs, not orthogonality or correspondence-isometry theorems.

The original conventions are Guy Henniart, *Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique* (2000), section 1.1 and footnote 1,
printed page 439 (actual supercuspidal classes and unitary characters);
section 1.2(2), page 440 (determinant scalar twists); and sections 2.5–2.6,
pages 446–447 (integral lattices and their specified-basis pairings).
Literature ID: `henniart-2000-simple-proof`; original SHA-256:
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The rank-wise equivalence packaging is an internal derivation from the
published supercuspidal twist and positive-form transport. Smooth
contragredience, all-unramified orbit data, global images, numerical finiteness,
and correspondence compatibility remain separate constructions or obligations.
