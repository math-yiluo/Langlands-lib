# CM-field algebras and rational similitudes

This module specializes the concrete involution and similitude constructions to
an actual totally imaginary quadratic extension `K/E` of number fields, with
`E` totally real. The two field carriers and the algebra carrier have independent
universes. It reuses Mathlib's number fields, quadratic extensions, embeddings,
centrality, simple rings, and finite-dimensional algebras.

`cmConjugation` constructs the nontrivial `E`-automorphism of `K` from Mathlib's
canonical CM conjugation. The bridge through
`CMExtension.equivMaximalRealSubfield` proves that this automorphism fixes the
specified `E`; it does not replace that field by an unidentified copy.
The involutivity, nontriviality, and compatibility with conjugation under every
complex embedding are proved from Mathlib's CM-field results.

`SecondKindInvolution E K A` is a real algebraic input: an `E`-linear
anti-involution of the given algebra `A` whose action on its embedded CM center
is the just-constructed conjugation. `CentralSimpleUnitaryData` adds the actual
centrality, simplicity, finite-dimensionality and dimension `n²` certificates,
with `n > 1`. It stores no output group, scheme, local system, or comparison
theorem. Existence of algebras with prescribed finite invariants and signatures
is not assumed or proved by this type.

`rationalInvolution` restricts scalars from `E` to `ℚ` using the explicit
scalar tower. `rationalSimilitudeFunctor` then constructs the group of pairs
`(g,c)` for every commutative rational test algebra `S`, using the actual algebra
`S ⊗[ℚ] A`. Thus the multiplier is in `Sˣ`, not in an arbitrary extension of
the totally real field.

Source: Harris 1999, Section 1, printed page 301 (PDF page 3), for the actual
CM extension, central simple dimension and second-kind condition, and the
rational multiplier. Kottwitz 1992, Section 1, page 654 (PDF page 2), for its
functor-of-points interpretation. The general algebra is central simple, as in
Harris Section 1; Kottwitz's division-algebra specialization is stronger.

This module imports the published `Langlands.Shimura.Unitary.Similitude`
and its `Involution` dependency. Their current Library files are unchanged
from the reviewed construction. `CMData`, `Signature`, and `Domain` form
one coherent contribution built over that published prerequisite; the
signature predicates are in `Signature`. All new code and intrinsic proofs
here are by Worker 57. Affine representability, the arithmetic levels,
canonical models and descent are not constructed in this module.

## Exact source and environment record

The retained originals are:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), pp.299-318;
  source `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- Harris, *Supercuspidal representations in the cohomology of Drinfeld upper
  half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
  pp.75-119; source `harris-1997-drinfeld-cohomology`,
  SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
  Invent. Math. 134 (1998), pp.177-210; source `harris-1998-local-langlands`,
  SHA-256 `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- Kottwitz, *On the lambda-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), pp.653-665;
  source `kottwitz-1992-lambda-adic-simple-shimura`,
  SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

The exact relevant passages and declaration correspondence are stated above.
The formal environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
