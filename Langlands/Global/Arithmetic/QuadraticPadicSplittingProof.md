# Actual splitting from two quadratic p-adic embeddings

`Langlands.Global.quadraticPadicSplitting` proves exactly the published
`QuadraticPadicSplittingStatement.{u}` in `SplitQuadraticPrerequisites`. The
theorem has no additional outer hypotheses. For every prime `p`, including 2,
and every number field `K : Type u` of rational degree two, two distinct
`ℚ`-algebra homomorphisms from `K` to `Padic p` yield
`HasSplitQuadraticPrime p K`.

The conclusion uses the actual height-one primes of `𝓞 K` and their actual
adic completions. It supplies two distinct primes containing `p`, exhaustion
of all height-one primes containing `p`, and ring equivalences from both
completions to `Padic p` that are continuous in both directions. The statement
does not require agreement between these equivalences and the initially
supplied embeddings. No topology on the global field is introduced.

The private helpers implement the following argument.

1. `rationalPrime_asIdeal` computes the rational place `r` selected by the
   inverse of `Rat.HeightOneSpectrum.primesEquiv` at `p`. Its ideal is generated
   by `p` in `𝓞 ℚ`, by Mathlib's construction of that equivalence and the image
   formula for a principal ideal. In `natCast_mem_iff_liesOver`, a prime of
   `𝓞 K` contains `p` exactly when its contraction is `r.asIdeal`. One direction
   uses maximality of the rational ideal and properness of the contraction;
   the other uses membership under contraction.
2. `tensorPair` extends two distinct rational algebra homomorphisms `φ, ψ`
   into a field `B` to the `B`-algebra map
   `B ⊗[ℚ] K → B × B` given on simple tensors by
   `b ⊗ x ↦ (b * φ x, b * ψ x)`. Choose `x` with `φ x ≠ ψ x`.
   For a desired pair `(s,t)`, set `c = (s-t)/(φ x-ψ x)`. The tensor
   `(s-c*φ x) ⊗ 1 + c ⊗ x` maps to that pair. This proves surjectivity.
   The scalar-extension dimension formula and `[K:ℚ] = 2` give equal
   source and target dimensions, so the finite-rank surjectivity criterion
   proves bijectivity.
3. `two_actual_places` uses the published `completedTensorComparison` at `r`,
   whose finite conjunct proves bijectivity of the canonical `finiteTensorMap`.
   This map has target the product of the actual fields `K_q` for
   `q : FinitePlacesAbove K r`. Compose its algebra equivalence with the inverse
   of the preceding evaluation equivalence. The image of `(1,0)` is an
   idempotent in this product that is neither zero nor one. It has a coordinate
   different from zero and a coordinate different from one. Each coordinate
   lies in a field, where an idempotent is zero or one, so these indices are
   distinct. They are actual primes lying over `r`.
4. `two_places_degree_one` applies the published
   `finiteLocalDegree_sum_le`: the sum of the dimensions `[K_q:ℚ_r]` is at most
   two. Each dimension is positive. The two distinct indices therefore both
   have dimension one, and any third index would make the sum at least three.
   This proves exhaustion as well as both degree assertions.
5. `completion_degree_one` applies
   `Algebra.finrank_eq_one_iff_bijective_algebraMap` to the canonical algebra
   map `ℚ_r → K_q`. Its inverse is a ring equivalence. The forward map is the
   existing continuous `FiniteExtension.completionMap`. The inverse is a
   linear map on a finite-dimensional Hausdorff vector space over the complete,
   nontrivially normed field `ℚ_r`, so
   `LinearMap.continuous_of_finiteDimensional` proves its continuity.
   The local nontrivially normed structure comes from the same actual adic
   valuation; the scalar action is the published continuous completion action.

The closing theorem transports the original embeddings into `ℚ_r` using
Mathlib's `Padic.adicCompletionEquiv`. Injectivity of this equivalence preserves
their distinctness. It applies the preceding helpers and composes each
degree-one completion equivalence with the inverse rational completion
equivalence. Continuity follows by composition. The rational-prime helper
translates lies-over membership and exhaustion into the exact clauses of
`HasSplitQuadraticPrime`.

This proof is an internal derived argument. It reuses the proved canonical
completed tensor comparison, its actual finite-place definitions, and the
local-degree upper bound from
`Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction`.
Mathlib supplies rational-place identification, tensor dimension formulas,
elementary ideal theory, and finite-dimensional continuity. No splitting
certificate, unproved local comparison, or additional axiom is assumed.
The target module and its import closure are unchanged.

The motivating passage is Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Inventiones Mathematicae 139
(2000), Section 3.3, printed page 449, second paragraph (PDF page 11).
That page was read from the registered original `henniart-2000-simple-proof`,
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
It chooses real and imaginary quadratic fields split at `p` with a disjointness
condition. The generic implication proved here is the project's stronger
arithmetic prerequisite, rather than a verbatim assertion of that passage.

Worker 1199 implemented the tensor, idempotent, degree, continuity and closing
arguments. Worker 60 contributed the two rational-prime helpers, folded into
this module from their checked private draft.
