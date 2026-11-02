# Actual product-Levi tensor comparison and induction

For positive ranks `a,b`, `binaryProductLeviTensorFunctor` is the existing
binary block-family functor followed by the existing finite external tensor
functor. Its target is the smooth category of the actual product Levi for
`BlockShape.binary a b ha hb`. The representation carrier is saturated at
`max uF uV`; the coefficient field is complex, and `F,T` are the existing
`PadicField` models. The group and carrier universes remain independent.

`binaryPositiveProduct_factorization` identifies the actual positive binary
normalized product functor with this external tensor functor followed by
actual normalized induction. It is equality of functors on both objects and
maps, using the already published definitions. Positive half-modulus
covariance and right translations are unchanged.

`ProductLeviTensorPrerequisitesStatement` explicitly requires finite-length
preservation and preservation of actual short exact sequences separately in
both factors. Given these prerequisites, `productLeviTensorMap` is the
integer-linear tensor comparison constructed by exact-K0 descent. Its object
formula is the actual external tensor representation class in product-Levi
K0. `ProductLeviTensorBijectiveStatement` names the additional bijectivity
obligation for this specific map. `productLeviTensorEquiv` constructs the
equivalence only from a proof of that target.

`productLeviInductionTensorMap` then applies the published actual
`Parabolic.normalizedInductionK0` to reach the K0 group of `GL_(a+b)`.
`productLeviInductionTensorMap_eq` proves that this composite agrees with
the tensor lift of the actual binary induction multiplication from
`GradedGrothendieck`, provided its explicit exactness target is supplied.
The proof compares actual object pairs, uses the K0 class formulas and the
published positive-product functor isomorphism. It does not assert an
isomorphism between a tensor product of K0 groups and the larger GL K0, or
between induced representations after interchanging the two factors.

The source is the product-Levi paragraph in Aubert 1995, printed p.2184,
read with the correction in `notes/henniart/aubert-duality-route.md`,
and Zelevinsky 1980, §1.7, printed pp.172–173.
The later Aubert induction compatibility is Theorem 1.7(2).
This module concerns two positive blocks because the published `BlockShape`
has strictly positive block sizes. Rank-zero multiplication and the actual
graded unit are retained separately by the all-ranks binary functor and
`gradedUnit` in `GradedGrothendieck`; a zero block is not inserted into an
invalid positive block shape.

The tensor descent and equivalence constructor are internal algebra with
their premises displayed. The actual induction K0 map reuses the published
finite-length and exactness theorems for the normalized parabolic functor.
Their existing GL representation-theoretic dependencies, together with
those of `binaryProductK0`, remain dependencies of the composite.
The prerequisites and tensor bijectivity are precise remaining proof
obligations; this construction does not treat them as consequences of an
external Chapter V structural package.
