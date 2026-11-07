# Fixed-height detection of the entire canonical induced space

This is derived supporting work by Worker 1369. It combines Worker 669's
actual unipotent restriction adapter with the coordinate stabilizer and
simple-root generation argument. Its proofs use existing Library results;
it makes no new assertion from external literature.

Let `k : Type u` be a field, `G` an affine group scheme over `Spec k`, and
`p : SplitPinning G` a supplied split pinning with finite root index. Assume
that its root datum has full integral coroot span. Write `rho` for the
resulting integral Weyl vector, `nu` for its polarization, and `chi` for the
canonical negative-rho coordinate on the actual dynamic parabolic `P(nu)`.
The canonical covariant space at exponent `m` is the entire coordinate
submodule `p.canonicalRhoCovariantSubspace hspan m`, defined by left
covariance under `P(nu)` with coordinate `chi^m`.

The module uses two existing actual representatives of the opposite
unipotent functor: the dynamic affine group `D` and the standard group `U`,
both for the cocharacter `-nu`. They need not be definitionally equal. The
represented-subgroup isomorphism identifies their inclusions into `G`.
Every evaluation equality below uses `AffineCoordinates.pointAlgebraHom`
on the original relative test scheme.

`exists_simple_of_mem_simpleRelativeRoots_oppositeRho` identifies every
intrinsic simple relative root of the negative chamber with the negative
of a simple root of the supplied base. This part needs no algebraic
closedness. The proof expresses the negated intrinsic root in the actual
root datum, uses the rho pairing to prove positivity, and applies positive
root induction. A decomposition into a positive root and a simple root
would contradict intrinsic simplicity. Thus the index lies in the base
support.

The remaining results assume `IsAlgClosed k`. Let `q` be an exponential
characteristic of `k` and `r : Nat`. There is no positive-height assumption.
The exponent is exactly `q^r - 1`, and the same height `r` is used in every
origin test and quotient.

`canonicalRho_eq_identityValue_of_originInvariant` starts with a coordinate
`f` in that entire canonical covariant space. Its premise is right
invariance under all intrinsic height-`r` origin points of `U`, at every
`G`-valued point of every relative test scheme. It concludes that the value
of `f` at every `U`-valued point equals its value at the identity point of
the same test. To prove this, the represented-subgroup isomorphism
transfers origin tests from `D` to `U`. The actual unipotent restriction and
Steinberg root degree cutoff give left invariance under each lifted negative
simple-root map. The preceding root identification supplies all intrinsic
simple roots. Smooth-root generation through the actual coordinate
stabilizer envelope then gives constancy on the whole group `D`, and the
isomorphism transfers it back to `U`. No affineness, reducedness or
nonemptiness condition is imposed on the test schemes.

`canonicalRhoFrobeniusRestriction` is the actual linear restriction from
the entire canonical covariant space at exponent `q^r - 1` to
`FrobeniusCoordinateModel.quotientAlgebra U q r`. It is literally the existing
`Dynamic.oppositeUnipotentFrobeniusRestriction` at these canonical data:
restrict to the actual opposite group, compare its coordinate algebras, and
pass to its characteristic-power augmentation quotient.

`canonicalRhoFrobeniusRestriction_injective` proves that this map is
injective. If it were not, the published nilpotent augmentation-distribution
argument would produce a nonzero vector in its kernel that satisfies the
all-test origin-invariance premise. The actual restriction coalgebra
preserves the counit, so the kernel vector has zero counit. The preceding
constancy theorem and the identity-evaluation formula show that its full
restriction to `U` vanishes. This equality of coordinates is detected at
the identity morphism of `U` by the global coordinate algebra equivalence.
The published injectivity of full opposite-unipotent restriction then
forces the original vector to vanish, a contradiction. No dimension,
nonzero highest-weight vector, irreducibility, or fixed-height injectivity
premise is supplied.

`finite_canonicalRhoCovariantSubspace` uses the constructed polynomial
coordinates of `U` to make its Frobenius quotient finite dimensional and
then transfers finiteness along the proved injection.
`finrank_canonicalRhoCovariantSubspace_le` gives the whole-space bound

`finrank k (p.canonicalRhoCovariantSubspace hspan (q^r - 1)) <=
  (q^r) ^ finrank k (Additive (lieKernel U k))`.

The quotient dimension formula is intrinsic to the actual Lie kernel of
`U`, rather than to a chosen polynomial presentation. The arbitrary field
universe `u` is retained throughout. The supplied pinning and full coroot
span remain hypotheses. This unit does not identify the Lie dimension with
a positive-root count, establish the universal existence of those supplied
data, prove a matching lower bound or irreducibility of the entire space,
or prove `SteinbergBigCellStatement`.
