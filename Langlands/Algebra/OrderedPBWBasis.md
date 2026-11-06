# Ordered finite-basis PBW over arbitrary fields

Authors: Worker 1687 and Worker 1431.

`Langlands.Algebra.UniversalEnveloping.orderedPBWBasis.{u,v}` proves exactly
`Langlands.Algebra.UniversalEnveloping.OrderedPBWBasisStatement.{u,v}`.
The coefficient field `k : Type u` and Lie algebra `L : Type v` have independent
universes. For every natural `n` and supplied basis
`b : Module.Basis (Fin n) k L`, the conclusion is linear independence and full
span of the published family `orderedPBWMonomial b` in Mathlib's actual
`UniversalEnvelopingAlgebra k L`.

The spanning argument is implemented in `OrderedPBWSpanning`. The quotient
generator map sends a Lie bracket to a commutator. Expanding the bracket in the
supplied basis expresses a word with an adjacent inversion as its swapped word
plus shorter words. Well-founded shortlex induction therefore expresses every
basis word as a linear combination of ascending words. Each ascending word is
the exponent word of its letter counts, and its evaluation is exactly the
published ordered monomial. Quotient surjectivity and tensor-algebra induction
show that basis words span the whole actual enveloping algebra.

For independence, `TriangularWordNormalization` constructs a linear normalizer
from well-founded triangular reductions and explicit coherence.
`OrderedPBWReduction` defines the concrete adjacent-inversion rules and proves
shortlex descent; its irreducibles are exactly the ascending words.
`OrderedPBWCoherence` proves that disjoint reductions commute and resolves the
overlap on three descending indices by Jacobi. `OrderedPBWNormalization`
specializes the generic construction, identifies its relation-span kernel,
proves that insertion preserves those relations, and derives the normalized
Lie commutator identity. The representation adapter uses these identities and
the universal property of the actual enveloping algebra to recover the
singleton exponent word from each ordered monomial. Specifically,
`PBW.normalAction` is normalized left insertion, `PBW.lieAction` packages
the proved commutator law, and `PBW.envelopingAction` lifts this Lie map.
Applying the action to the empty word defines the linear `PBW.coefficientMap`.
Word induction and ascending fixedness prove that this map sends each actual
ordered monomial to its exponent word's unit singleton. Distinct exponent
vectors give distinct words, whose singletons are linearly independent.
Pullback along this linear map proves
`PBW.orderedPBWMonomial_linearIndependent`.

The final Lean proof introduces all the variables of the target proposition
and pairs the independence theorem with `orderedPBWMonomial_span`. No
characteristic restriction or positivity assumption on `n` is added. In
particular, the proof uses the alternating Lie-ring bracket and Jacobi without
division, so characteristic two is included. When `n = 0`, the empty word and
empty product provide the same argument.

The published target cites Shepler and Witherspoon, *Poincare-Birkhoff-Witt
Theorems*, retained 2014 author PDF, Section 2, printed/PDF pages 2–3. This proof
implements the explicit normalization and representation route above, using
only ordinary Lie-algebra axioms and Mathlib's actual tensor-quotient
construction. It supplies no PBW, normal-form, injectivity or polynomial
equivalence assumption.
