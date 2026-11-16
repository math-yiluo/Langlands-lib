# Rank-one laws for actual supplied opposite roots

This internal derivation concerns actual opposite root parametrizations
in an affine reductive group over an arbitrary commutative local ring.
It assumes a closed fibrewise maximal coordinate split torus and its
fibrewise root datum. The supplied three-factor Weyl product must act by
the corresponding root reflection.

Rank-one laws are preserved by a homomorphism of ambient groups: compose
each of their four point equalities with that homomorphism, using the
constant Weyl product and root-point composition identities.

For an isolating cocharacter, choose the actual pointed etale unit cell
at the closed residue point and its affine refinement. The associated
Weyl data have beta one by the supplied-action uniqueness result.
Their actual coroot is the fixed-exponent coroot, so the generic
beta-one bridge gives all four laws on every scheme test over the
coefficient algebra. The affine etale projection is surjective, because
it retains a point over the closed point of the local base. Its flat
pullback is faithful. The all-test descent theorem therefore proves the
laws for the lifted roots in the actual centralizer over the original
ring. Composition with the centralizer inclusion proves them in the
ambient group, in the original supplied coordinates.

`LocalSplitRootPairLawsStatement` asserts these laws for every root and
every supplied opposite pair satisfying the stated Weyl action.
`localSplitRootPairLaws` proves it without an isolating-cocharacter
hypothesis. Finiteness and reducedness of the fibrewise root datum give
an exponent vector whose zero roots are precisely the chosen root and
its negative. Apply the centralizer argument with this vector.

The argument retains nilpotents and imposes no reducedness,
noetherian, henselian or characteristic hypothesis. The full local
Isomorphism Theorem remains separate.
