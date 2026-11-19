# Absolute convergence of the complex equal-rank integrals from simple-root bounds

`complexLocalEqualConvergenceReduction` proves an implication to the exact
Library statement `ComplexLocalEqualFunctionalEquationStatement`. It retains
three open premises.

- `ComplexLocalWhittakerUniformGrowthStatement` asserts a fixed growth
  exponent across the simple-root derivative words of each inducing vector
  for each Whittaker intertwiner. The bound for a word is uniform over the
  right unitary factor.
- `ComplexLocalEqualPrimalContinuationStatement` supplies a meromorphic
  continuation of the primal integral given convergence on a right
  half-plane. The continuation agrees on that half-plane or a smaller
  right half-plane.
- `ComplexLocalEqualMeromorphicEquationStatement` supplies the codiscrete
  functional equation for the two continuations agreeing with the original
  and dual integrals on a common right half-plane.

Every element of the model is continuous because each intertwiner has
smooth values and the continuous functions form a submodule. Opposite
characters make the product invariant under left unipotent multiplication.
Differentiating the Whittaker equivariance along each simple root
expresses the product of root ratios as a derivative word. The uniform
growth premise bounds those words and proves the logarithmic simple-root
estimate throughout the model. Together with the last-row Schwartz estimate,
this supplies the logarithmic kernel bound. The determinant weight and
the summation over compact logarithmic Iwasawa boxes then prove absolute
convergence for every compatible quotient measure on a right half-plane.

Apply the continuation premise and restrict the convergence half-plane
if needed to get agreement. The published holomorphy implication supplies
complex differentiability there from absolute convergence. The duality
reduction applies the same primal argument to the two dual coefficients
and the exact Fourier-transformed test function. It uses the common
right half-plane of convergence and agreement to apply the equation
premise and obtain the unchanged target.

The convergence estimates reflect Jacquet's *Archimedean Rankin–Selberg
integrals* (2009), printed and PDF pp. 11 and 14–16, especially (3.3),
Lemma 3.5 and Proposition 3.1. The target is Theorem 2.1 (i)–(iii) on p. 6.
The proof implements the analytic implication in the Library's quotient
and model, using a box estimate for the measure and the fixed logarithmic
coefficient bound. Establishing uniform growth for the Library's model and
proving the two meromorphic premises remain open.
