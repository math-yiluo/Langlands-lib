# Closure of continuous translation-finite functions

`Langlands.RankinSelberg.FiniteFunctionClosureStatement G H` states three
closure facts for complex functions on monoids `G` and `H`, each supplied with
an arbitrary topology. Their type universes are independent. No continuity of
the monoid operations is assumed or needed for this statement.

For a function `f : G → ℂ`, the finite-function condition is exactly the
conjunction of continuity and finite dimensionality over `ℂ` of

\[
\operatorname{span}_{\mathbb C}\{a\mapsto f(ba):b\in G\}.
\]

The translation convention is left multiplication in the argument, matching
`CoefficientTorusExpansion` and `WhittakerTypeAsymptoticStatement` when `G` is
the multiplicative torus. The predicate is local to the proposition; it does
not replace the existing conditions in those statements.

The three clauses assert:

1. The pointwise product of two finite functions on `G` is a finite function.
2. If `h : H →* G` is continuous, pulling a finite function back along `h`
   gives a finite function on `H`. No injectivity or surjectivity is required.
3. A continuous monoid homomorphism `χ : G →* ℂ` is a finite function on `G`.
   On a group its values are automatically units. The formulation also allows
   general monoids and does not assert finite dimensionality of all functions.

This is an internal elementary algebraic interface for the Rankin–Selberg
argument, not a theorem attributed to an original paper. The first clause is
motivated by containing product translates in the span of products of two
finite-dimensional spaces. The second uses the linear map given by
precomposition. For the third, every translate is the scalar multiple
`χ b • χ`, so its span is at most one-dimensional. These observations explain
the intended assertions; this statement module does not supply their proofs.

In the JPSS application, these clauses permit combining the two finite-function
families in coefficient expansions, changing torus coordinates, and multiplying
by a continuous multiplicative weight once that weight has been constructed.
The arbitrary topologies permit specialization to the supplied field data
`T`, and the independent monoids permit coordinate maps between different torus
dimensions. The statement does not construct the particular inverse-modulus
character or its continuity proof, prove a Whittaker expansion, or assert
Mellin convergence, rationality, a common denominator, or a normalized
generator. Uniform denominators for the entire coefficient family remain
separate analytic obligations.
