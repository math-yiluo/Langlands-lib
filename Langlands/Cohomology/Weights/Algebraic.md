# Weight factors over the coefficient field

Author: Worker 41. This contribution defines the coefficient-field construction
and proves its intrinsic laws. It does not complete the global-family task.

The construction `algebraicWeightFactor q w P` is the product of the normalized
irreducible factors of `P` that are pure of weight `w`, with all multiplicities
retained. It lies in the original number field's polynomial ring and does not
choose a complex embedding. Its specification uses the actual purity predicate
defined in the polynomial prerequisite.

The proof route for descent first shows that a root of the rational minimal
polynomial of a Weil number is again a Weil number of the same weight. For a
monic irreducible polynomial over the coefficient field, one Weil root implies
purity at every embedding: identify the polynomial with that root's minimal
polynomial over the coefficient field, show that it divides the rational
minimal polynomial after extending coefficients, and apply this divisibility
at each other coefficient embedding. This argument does not assume that a
general automorphism of the complex numbers preserves the complex absolute value.

The construction laws assert monicity, purity, divisibility of a monic input,
and multiplicativity for nonzero inputs. Purity is preserved by products,
including the empty product.

The comparison `map_algebraicWeightFactor` has the following explicit
hypotheses. Let `q > 1`, let `P` be monic over a number field `L`, and choose
embeddings `iota, kappa : L -> C`. Suppose each root of `iota(P)` is a Weil
number of some integer weight; the weight may depend on the root, but being a
Weil number includes the condition at all rational conjugates. Then

\[
  \kappa(\operatorname{algebraicWeightFactor}(q,w,P))
  =\operatorname{complexWeightFactor}(q,w,\kappa(P)).
\]

The proof obtains a complex root of each normalized irreducible factor,
using algebraic closure. Divisibility places this root among those of `P`.
The minimal-polynomial argument makes that irreducible factor pure at every
embedding. For each such factor, complex weight selection returns the whole
factor or the constant polynomial `1`. Distinct integer weights have distinct
radii because `q > 1`. Induction over the finite multiset of factors and
multiplicativity of complex weight selection finish the comparison.

The comparison is proved in Lean, rather than assumed as an axiom or as a field
of an object. The polynomial chosen over `L` is independent of both complex
embeddings. Neither the definition nor this comparison asserts a source of the
root-purity hypothesis in Galois representations or cohomology.

This is derived algebraic infrastructure for Kottwitz 1992, Theorem 1(b), p.657,
and Section 6, equation (6.1) and its coefficient-field factorization, p.664.
The original source has literature ID
`kottwitz-1992-lambda-adic-simple-shimura` and SHA256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
The polynomial factorization construction and proof route are authored here;
they are not a transcription of the full cohomological theorem.

Native compilation in the pinned environment terminated with exit 0 and no
diagnostics. The factor definition and the elaborated types of its construction
laws were inspected. The exact descent theorem uses only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; no project axiom is introduced.
These are development checks, not independent semantic acceptance.

The project dependency `Langlands.Cohomology.Weights.Polynomial` is accepted
artifact `f1e2d792-01c3-4385-9bf4-4ae9c9e5464f`, version 1, independently
approved by Reviewer 124 and published in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
Its effective integrated snapshot is
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`,
integration `ce5a00e3f0724675ad6e9ae202fe5cf7`. Its exact Lean SHA256 is
`47a03391e9b60f456f2b30133179940bb3fa75ee2b8c740b03641aaa0742964f`,
and paired Markdown SHA256 is
`0d2b84fde43d92f8476a81d37d4725c91a7f347a77ae88629704307846513a6b`.
The current-Library membership check reports no changed or missing file and
no unavailable dependency. The integrated content matches the locally checked
source exactly.
The Mathlib dependency is the pinned environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

No global representation, Shimura cohomology, Hodge-Tate comparison, or
automorphic transfer is defined by this polynomial construction.
