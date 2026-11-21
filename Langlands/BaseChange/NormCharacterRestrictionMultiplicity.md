# Restricting finite abelian characters to local norm characters

`NormCharacterRestrictionMultiplicityStatement` describes the restriction of complex characters of a finite abelian group along a local map whose kernel is the actual norm image. The restrictions are exactly the norm-trivial characters. Each one has a fiber of cardinality equal to the index of the local image in the finite abelian group.

A norm-trivial character factors through the image of the local map. The Mathlib finite abelian duality theorem extends it to the ambient group. Multiplication by the inverse of one extension identifies the whole fiber with the kernel of restriction. Finite abelian duality identifies the latter cardinality with the order of the quotient. This supplies the multiplicities for the finite factors in the use of Arthur–Clozel, Chapter 1, Lemma 6.13, once the actual local reciprocity map and its global image are identified.
