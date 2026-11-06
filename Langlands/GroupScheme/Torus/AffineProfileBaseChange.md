# Actual geometric torus profiles under arbitrary affine base change

This internal module compares the actual adjoint profiles of a smooth affine
group family and a supplied standard split torus after every specified affine
base morphism. The original ring and the new ring are arbitrary; neither
reducedness nor noetherian hypotheses are imposed. Ambient fibres may be
disconnected.

For `b : Spec A → Spec r`, `affineExponentWeightBaseChangeEquiv` makes `A`
an `r`-algebra using `Spec.preimage b` and constructs the actual linear
equivalence from the scalar extension of each original exponent weight
module to the corresponding actual weight module of the scheme pullback.
The torus map in that pullback uses the existing canonical split-torus
base-change isomorphism, namely
`RelativeCocharacterCentralizer.baseChangedTorusHom`. This notation for the
actual base-changed torus map does not depend on any cocharacter vector.

The construction starts with the published actual scalar-extension
equivalence for `algebraBaseMap r A`. Full faithfulness of the affine
spectrum functor identifies that base map with the specified `b`.
Transport along this equality gives the stated equivalence with its exact
target group and target torus map; it does not substitute an abstract
isomorphic group or an unrelated module.

`exponentWeightRank_affineBaseChange` proves that the rank at a stalk of
that actual pulled-back weight module is the original rank at the image
point. The proof uses invariance of stalk rank under this linear
equivalence and the finite-flat-module stalk-rank base-change theorem.
The original weight modules are finite projective by the previously
implemented smooth-affine Lie-module and actual weight decomposition
results.

`finrank_geometricIdentityWeight_affineBaseChange` compares the actual
weight dimensions of the actual geometric identity components at points
lying over one another. Each dimension equals its actual relative weight
rank, and the rank equality just proved identifies the two. Thus the
comparison retains the algebraic closures of the respective actual residue
fields chosen by each geometric-fibre definition; no equality or prescribed
embedding of those chosen closures is assumed.

`geometricExponentRoots_affineBaseChange` proves equality of the complete
integral-indexed actual root supports at such points. Actual root membership
is exactly a nonzero integer character vector and nonzero actual weight
rank. The common integer coordinate set and the stalk-rank equality give
the asserted equality.

For an actual closed torus inclusion, its canonically identified pullback
is closed. `geometricSelfCentralizingTorusLocus_affineBaseChange` then proves
that the pulled-back family's actual geometric self-centralizing-torus
locus is exactly the inverse image of the original locus. It applies the
proved zero-weight-rank criterion on both sides and the same rank equality.

The provenance is internal: this is an affine-scheme-map adapter for the
published actual weight scalar-extension equivalence and stalk-rank
theorems, followed by their actual geometric root and self-centralizer
interpretations. These comparisons support changes of base in the local
openness assembly; they do not construct the initial torus or forward
field reflection data and do not prove the general openness theorem.
