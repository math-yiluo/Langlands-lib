# Actual graded exact K0 and induction multiplication

This module constructs the direct sum of the published exact finite-length
Grothendieck groups of `GL_n(F)` over every natural rank, including zero.
It uses the existing complex `PadicField` models with independent universes
`uF` and `uV`, and representation carriers in `Type (max uF uV)`.
It does not extend these models to all non-archimedean local fields.

`GradedGrothendieckGroup` is the actual direct sum, not a free group on labels.
`gradedInclusion` is its canonical integer-linear homogeneous inclusion.
`binaryProductK0` descends the published all-ranks
`T.binaryNormalizedProductFunctor`, using the generic bilinear exact-K0
construction. `binaryProductK0_classes` identifies its values with the
classes of the actual induced representations.

Finite-length preservation is supplied by the published
`Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength`.
`BinaryProductExactnessStatement` is the separately named remaining proof
obligation: actual short exact sequences must remain short exact with a
fixed finite-length factor, in each variable. The construction takes a proof
of this target explicitly; naming it does not prove it.

`gradedMultiplication` is the double direct-sum extension of these actual
homogeneous products. The homogeneous formula places the product of ranks
`a` and `b` in rank `a+b`. `gradedUnit` is the class of the published actual
one-dimensional trivial representation on `GL_0`, whose finite length is
proved from its finite-dimensional carrier. The existing binary left and
right unit equivalences remain the representation-level inputs to the unit
laws after the necessary rank and carrier transports.

`GradedInductionRingLawsStatement` names associativity, commutativity and both
unit identities for this specific multiplication. Bilinearity already gives
distributivity and the zero identities. `gradedInductionRing` constructs the
commutative ring from a proof of those laws. It does not equip an unrelated
carrier with an arbitrary assumed ring multiplication. `gradedOperator`
constructs the canonical additive extension of a family of actual
homogeneous K0 endomorphisms, with its homogeneous formula.

The source motivation is Aubert 1995, Definition 2.1 and Theorem 2.3,
printed pp.2184–2185, and Zelevinsky 1980, §1 and Corollary 7.5.
The published product uses upper parabolics, right translations and positive
half-modulus covariance, including the explicit tensor models at rank zero.
No normalization is changed here. Induction multiplication takes values in
the larger GL K0; a tensor comparison with the product-Levi K0 is a separate
construction and cannot be replaced by an equivalence with that larger GL.

The direct-sum constructions and bilinear descent are internal algebra.
The finite-length input has actual representation-theoretic dependencies:
in positive ranks, the cited binary lemma uses
`Classification.admissibleFiniteLengthProductPreservation` and
`finiteLengthAdmissibility`. The former uses finite tensor factor matching,
composition-series length and
`Classification.normalizedInductionFiniteLength`; its irreducible
product helper uses `irreducibleProductEmbedding`, ordered product
regrouping, the supercuspidal tensor theorem and normalized cuspidal
induction length. Rank zero uses finite-dimensional inert tensor factors.
These are published GL inputs, not an external Chapter V structural
boundary. A detailed transitive dependency ledger accompanies the final
comparison notes; this construction does not claim classification
independence or that the exactness and ring-law targets are proved.
