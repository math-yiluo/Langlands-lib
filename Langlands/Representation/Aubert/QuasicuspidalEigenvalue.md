# Aubert eigenvalues on quasicuspidal and induced classes

Author: Worker 76.

This internal helper module proves that the unadjusted Aubert operator on an
actual product Levi acts on any finite-length quasicuspidal smooth complex
representation with eigenvalue `(-1)^(n - B.length)`. The published induction
commutation theorem gives the same eigenvalue on its normalized induced
class in the exact finite-length Grothendieck group of `GL_n(F)`.

## Implemented argument

The refinement `CuspidalSupport.MinimalRefinedJacquet.wholeRefinement B`
keeps each outer block as one inner block. Every inner parabolic is full,
so the refined parabolic and its refined Levi are full.
Conversely, fullness of a refined parabolic implies that every inner
parabolic is full. The published block-index lemma makes its block indices
subsingleton. The positive rank of each outer block rules out an empty
inner shape, leaving exactly one inner block. Its total-size equation then
identifies the shape with the corresponding whole refinement. The only
record-extensionality helper is a direct comparison of lengths and sizes;
the positivity and total-size fields are proof-irrelevant.

The published `fullRefinedJacquetEquiv` and
`fullRefinedInductionEquiv` identify actual normalized induction after
Jacquet restriction for this whole refinement with the original smooth
representation; their composition is exposed as
`wholeRefinementInductionJacquetEquiv`. Those equivalences prove that both normalization factors
are one on the full refinement, remove the trivial unipotent quotient and
evaluate the actual smooth induction at one, with inverse given by the
orbit function. Applying the exact-class isomorphism relation proves
`refinedInductionJacquetK0_wholeRefinement`.

For every other refinement, the refined parabolic is proper.
Quasicuspidality says its actual unipotent coinvariant carrier is
subsingleton. The class of that zero representation vanishes in the exact
Grothendieck group, by the published
`IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton`.
Thus `normalizedRefinedJacquetK0_quasicuspidal` kills every proper term.
The alternating sum reduces to its sole whole-refinement term. Its exponent
is `n - B.length`, since there is one inner block in each outer block.
This proves `alternatingOperatorOnLevi_quasicuspidal`.

Finally, evaluating the published unconditional `inductionCommutation`
identity on the input class and using integer linearity proves
`alternatingOperator_normalizedInductionK0_quasicuspidal`.

## Scope and provenance

These are elementary consequences of the published actual refined functors,
full-refinement equivalences, finite-length preservation, exact-class
relations and induction commutation. They do not assert signed effectivity,
irreducible preservation or exactness of a duality complex, and do not use
any pending version of those conclusions.

The parameters are arbitrary primes, supplied p-adic fields and
`F.TopologicalData`, with independent `uF,uV` and carrier universe
`Type (max uF uV)`. Every rank, including rank zero and the empty product
Levi, is included. Only finite group-algebra length and
`IsLeviQuasicuspidal` are assumed of the input; irreducibility,
admissibility, central character and finite vector-space dimension are
unnecessary. Irreducible inputs may obtain finite length from the existing
generic theorem.

The imported actual induction uses upper block parabolics, positive
half-modulus covariance and right translation; normalized Jacquet uses
upper-unipotent coinvariants and inverse half-modulus action. The operator
is the published unadjusted alternating sum. The proof does not invoke
segment classification, multisegment exhaustion, Langlands quotient
coverage, tempered block uniqueness or square-integrable classification.
