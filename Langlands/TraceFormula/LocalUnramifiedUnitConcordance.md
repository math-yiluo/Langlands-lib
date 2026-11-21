# Unit concordance at an unramified finite place

`localUnramifiedUnitConcordance` proves `LocalUnramifiedUnitConcordanceStatement`.
It takes the field unit fundamental lemma as a premise. For a cyclic
number-field extension `L/K` at a finite place `v` where every place above
`v` has ramification index one, it proves `AreConcordant` for the local
unit functions on `GL_n(K_v)` and `GL_n(LocalBaseChangeAlgebra K L (.inr v))`.
The base uses the p-adic spherical unit and Haar measure from
`CompletionPadic.padicField v`. The upper function is the indicator of
the subgroup over `localIntegers K L v`. The upper Haar measure may be
any Haar measure giving that subgroup mass one.

The proof takes cyclic coordinates in copies of an actual completion
`L_q` above `v`. The arithmetic ramification index one identifies the
canonical p-adic ramification indices of `L_q` and `K_v`. The
completion topologies agree with the canonical p-adic topologies, so
the cyclic coordinates give the continuous algebra maps needed by
`cyclicProductUnitReduction`.

The comparison of the completion and p-adic valuations identifies the
integer rings. Testing the entries of a matrix and its inverse
identifies the upper integral subgroup with the product of the
spherical subgroups of the factors. In these coordinates the transported
product Haar measure gives the upper integral subgroup mass one. Haar
uniqueness identifies it with the supplied upper measure, and the
subgroup comparison identifies the unit indicators.

This internal reduction connects the field and cyclic-product unit
comparisons of Henniart–Lemaire, I.3.2, printed pp. 25–26
(PDF pp. 33–34), with the finite-place algebras used in I.6.1,
p. 39 (PDF p. 47). The proposition uses general linear groups in
matrix coordinates.
