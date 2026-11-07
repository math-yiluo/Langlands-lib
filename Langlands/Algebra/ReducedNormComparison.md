# Comparison with arbitrary splitting fields

This internal helper starts with a finite Galois splitting chart `e` over `L/K`
and the descended determinant law from `ReducedNormEvaluation`. It proves its
comparison with every splitting field `F/K` and every `F`-algebra matrix chart
`f` of the same finite nonempty matrix size. The arbitrary splitting field need
not be finite, separable, normal, or algebraic. Coefficient fields, the algebra,
indices and test algebras may live in independent universes.

`extendSplittingChart e E` extends the supplied chart to an actual `E`-algebra
equivalence for any compatible commutative `L`-algebra `E`. Its underlying
algebra map is exactly `splittingMap e E`, with pure-tensor formula
`r tensor a` mapping to `r` times the coefficient extension of `e(1 tensor a)`.
Bijectivity is proved by composing the linear tensor-cancellation equivalence,
the tensor product of the identity with the original chart, and the standard
matrix/tensor equivalence. Identifying this composite with `splittingMap` by
tensor induction establishes the algebra equivalence. In particular the
construction works for the possibly noncommutative original algebra `A`.

`chartPolynomial_baseChange` proves that extending the chart extends the
coefficients of its actual determinant polynomial. For a common field `E`
containing `L` and `F` compatibly over `K`, `descendedPolynomial_map_common`
extends both chart polynomials to `E`. Polynomial chart independence over `E`
identifies them. Injectivity of `F → E` reflects polynomial equality back to
`F`. To obtain such an `E` without assuming it, the next theorem uses an
algebraic closure of `F`: the algebraic extension `L/K` admits a `K`-embedding
there. This embedding equips the closure with a compatible `L`-algebra
structure. Thus `descendedPolynomial_map_chart` proves the required
coefficient identity for every splitting field and chart.

`normFromGalois_eq_det_of_chart` then proves determinant comparison over every
further commutative `F`-algebra `R`, with compatible `K` structure. It extends
the polynomial coefficients through `F`, uses the just-proved coefficient
identity and the generic determinant evaluation formula, then identifies the
matrix sum using the finite basis-coordinate expansion of the tensor. This
covers nonreduced algebras, zero rings and arbitrary elements of `R tensor_K A`.
It does not infer polynomial equality from field-valued points.

When `F/K` is also finite Galois, injectivity of `K → F` and the same comparison
prove `descendedPolynomial_splitting_independent`. Combining this with the
previous basis-independence theorem gives
`normFromGalois_splitting_independent` on every commutative `K`-algebra, allowing
different finite coordinate-index types. Both splitting fields and both
charts may be chosen independently. Unconditional existence of a splitting
chart remains a separate prerequisite for the final construction.

The source convention is Milne, *Algebraic Groups* (2022 corrected reprint),
Remark 24.25, printed p. 523 / PDF p. 534, registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The retained author errata of 2026-11-04 do not correct this passage. The
common-overfield comparison and its polynomial and all-test extensions here
are an internal derivation of Milne's chart-independent determinant convention.
The algebraic closure is used only to compare actual polynomials; descent to
`K` still uses the finite Galois fixed-field argument in `ReducedNormDescent`,
which applies in arbitrary characteristic and over imperfect fields.
