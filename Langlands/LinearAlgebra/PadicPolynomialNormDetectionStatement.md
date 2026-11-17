# Detecting a p-adic polynomial by norms of resultants

`Langlands.LinearAlgebra.PadicPolynomialNormDetectionStatement` is an unproved
proposition. For every prime natural number `p`, it considers two monic
polynomials `P` and `Q` over the actual p-adic field `ℚ_[p]` with equal natural
degrees. It asserts that `P = Q` if, for every integer polynomial `F`, the
p-adic norms of `resultant P F` and `resultant Q F` agree. In Lean, the integer
coefficients of `F` are mapped into `ℚ_[p]` by `Int.castRingHom`. The norm is the
standard real-valued norm on `ℚ_[p]`.

The source is J. S. Milne, *Abelian Varieties*, January 2, 2022 author revision,
§12, Lemma 12.10, p.23 (also one-based PDF page 23), source ID
`milne-abelian-varieties-1986-author-2022`. The complete registered errata
snapshot was read; its corrections are incorporated in this revision. Milne
states the hypothesis using the products of `F` evaluated on all roots of
`P` and of `Q`, with multiplicity, in a splitting extension. He cites Lang
1959, VII, §1, Lemma 1, for the proof. This file relies on Milne's stated
lemma; it does not claim to have checked Lang's original proof.

The resultant formulation is a translation of that root-product hypothesis.
For monic `P`, its resultant with `F` is the product of `F` over the roots of
`P`, counted with multiplicity. This identity can be used after passing to a
splitting field; Mathlib supplies `Polynomial.resultant_eq_prod_eval`.
The resultant belongs to the base field, so the statement needs no choice
of algebraic closure or extension of the norm. The same observations apply
to `Q`. The two optional degree arguments of `Polynomial.resultant` are
omitted, so Lean uses the actual natural degrees of its two arguments.

The hypotheses include all integer polynomials, including constants and the
zero polynomial. They do not restrict to tests of the form `X - n`. Equal
degree and monicity are explicit hypotheses, as in the source; repeated
roots are allowed. This statement supplies no proof of norm detection or
of the geometric endomorphism trace comparison that motivates it.
