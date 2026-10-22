# Polynomial roots of invertible complex endomorphisms

`Langlands.complexPolynomialRoots.{u}` proves the complete published proposition
`Langlands.ComplexPolynomialRoots.{u}`. For every finite-dimensional complex
vector space `V : Type u`, every invertible endomorphism `A`, and every positive
natural number `n`, it produces `p : Polynomial ℂ` with

\[
  (p(A))^n=A.
\]

The proof imports the statement from
`Langlands.LinearAlgebra.ComplexPolynomialRoots`. It preserves the arbitrary
carrier universe, all quantified instances, the polynomial witness, and the
zero-dimensional case. No diagonalizability or semisimplicity assumption is used.

## Implemented argument

Let `m = minpoly ℂ A`. Cayley–Hamilton makes `A` integral, so `m` is nonzero.
Invertibility gives injectivity of `A`, and
`LinearMap.minpoly_coeff_zero_of_injective` gives `m(0) ≠ 0`.
Choose a squarefree polynomial `g` and an exponent `k` with
`g ∣ m` and `m ∣ g^k`, using
`exists_squarefree_dvd_pow_of_ne_zero`.

Algebraic closedness of the complex numbers supplies a scalar nth root `r(a)`
for every complex number `a`. Lagrange interpolation on the finite set of roots
of `m` supplies a polynomial `q` such that `q(a) = r(a)` at each root of `m`.
Thus every root of `g` is a root of `q^n - X`. The private supporting lemma
`squarefree_dvd_of_eval_zero` turns this root inclusion into divisibility:
over the complex numbers `g` splits, and squarefreeness makes its root multiset
have no repetitions. Consequently `g ∣ q^n - X`, and hence
`m ∣ (q^n - X)^k`.

The polynomials `m` and `q` are coprime. Indeed, if `m(a) = 0` and `q(a) = 0`,
then `a = r(a)^n = 0`, contradicting `m(0) ≠ 0`. The formal proof applies
`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`.

Now work in the commutative complex algebra `B = Algebra.adjoin ℂ {A}` and
write `a : B` for its distinguished element with underlying endomorphism `A`.
Evaluation of the preceding divisibility gives

\[
  (q(a)^n-a)^k=0.
\]

Evaluation of a Bezout identity for `m` and `q`, together with `m(a)=0`,
shows that `q(a)` is a unit in `B`. The scalar `n` is a unit in `B`, because
it is the image of the nonzero complex number `n`. The derivative of the
polynomial `F = X^n - C(a)` over `B`, evaluated at `q(a)`, is therefore the
unit `n q(a)^(n-1)`.

Mathlib's `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero` now
applies: `F(q(a))` is nilpotent and `F'(q(a))` is a unit. Its Newton iteration
provides `b : B` satisfying `F(b)=0`, hence `b^n=a`. Only the existence part
of this theorem is used. Finally, `Algebra.adjoin_eq_exists_aeval` expresses
the underlying endomorphism of `b` as `p(A)` for a complex polynomial `p`.
Applying the inclusion of `B` in the endomorphism ring to `b^n=a` proves
the required equality.

The same argument handles the zero-dimensional carrier. It never assumes
that the endomorphism ring or `B` is nontrivial; the minimal polynomial can
be the constant polynomial `1`, and the interpolation set can be empty.

## Provenance

This is an internal derived proof of the proposition motivated by Henniart's
1980 argument, as documented with its original citation in the imported
statement's Markdown. The implementation uses Lagrange interpolation and
Mathlib's algebraic Newton lifting theorem rather than the truncated local
series and Chinese remainder construction suggested there. The private
divisibility lemma is an elementary consequence of Mathlib's splitting and
separability results, included only to support this proof.
