# Eight-dimensional unital composition data

Author: Worker 177.

`CayleyDatum K` consists of a bilinear multiplication on the actual vector
space `Fin 8 → K`, a two-sided identity vector, and a quadratic form with
norm one on the identity, multiplicative norm, and zero radical for its
polar bilinear form. No associativity or invertibility of two is assumed.
In particular this permits Cayley algebras in characteristic two. The
datum supplies an actual algebra multiplication and norm; it is not an
abstract label for a group type or a local index.

The source is Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*,
Section 33.B, printed p.456 / PDF p.479, Definition and Proposition 33.9.
There a unital composition algebra of dimension greater than two is
specified by a nonsingular multiplicative quadratic norm, and
alternativity follows from these conditions. Section 33.C,
Theorem 33.17, printed pp.459–460 / PDF pp.482–483, identifies the
eight-dimensional case as Cayley. The fixed coordinates are a derived
choice of basis on this finite-dimensional vector space. The explicit
norm-one identity condition agrees with the source and is included in
the data. This module does not prove the classification or alternativity.

`structureConstant i j k` is coordinate `i` of the product of the standard
basis vectors `j` and `k`. `multiplicationOver φ` extends these constants
along a ring homomorphism `φ : K →+* A` to any commutative coefficient
ring, including algebras
with nilpotents. It evaluates the resulting bilinear multiplication by
a double sum; `unitOver φ` maps the identity vector coordinate by
coordinate. The theorem `multiplication_apply_eq_sum` expands each vector
in the standard basis and uses bilinearity. It proves
`multiplicationOver_self`, so over `K` this formula is exactly the
original multiplication. `unitOver_self` gives the same compatibility
for the identity vector.

`IsAutomorphismMatrix` says that an invertible matrix acting on column
vectors fixes the extended identity and preserves the extended
multiplication on every pair of vectors. Its definition does not impose
an extra norm-preservation equation. The underlying notion is an
automorphism of the unital algebra, as in the source's Theorem 26.19,
printed p.373 / PDF p.396; Proposition 33.9 makes the norm intrinsic to
the multiplication, but that implication is not proved here.

`IsAutomorphismRepresentation` is a predicate on a homomorphism of
actual group schemes into the actual `GeneralLinear.groupScheme`
in dimension eight. It requires a closed immersion and identifies
its range on every test scheme with exactly the preceding equations
over that test scheme's algebra of global sections. The existing
`GeneralLinear.pointsEquiv` supplies the actual matrix comparison.
Thus the comparison retains nonreduced coefficient rings and is not
merely an identification of rational points. Closedness and this
all-test identification are hypotheses of the predicate; this module
constructs no representing group and asserts no such homomorphism
exists.

The coordinate extension and all-test formulation are derived
interfaces for the source's algebra automorphism functor. The original
Theorem 26.19 describes an equivalence between Cayley algebras and
simple groups of type G2 over an arbitrary field, using descent of
the multiplication tensor. No such classification theorem, local
splitting theorem, or rank-one exclusion is proved by these definitions.

The retained official author errata and the page-sorted unofficial
comments were checked for the cited passages. The unofficial comment
about a nonexistent reference in the proof of Proposition 33.6 does
not affect this module: that proposition is not used.
