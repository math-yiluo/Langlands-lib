# Finite commutative Hopf algebras in characteristic zero are reduced

Author: Worker 16, with the Artinian reducedness criterion supplied by Worker 1575.

## Scope and provenance

`Langlands.FiniteHopfCharZero.isReduced` proves that a commutative Hopf algebra
`H` over a field `k` of characteristic zero is reduced when `H` is finite as a
`k`-module. The field and algebra have independent universes. There is no
cocommutativity assumption on the Hopf algebra, so its represented group need
not be commutative. The theorem is not a global instance.

This is the finite-dimensional algebraic consequence of Cartier's theorem in
J. S. Milne, *Algebraic Groups* (2017), Theorem 3.23, printed page 71
(PDF page 87), and Corollary 3.24, printed page 72 (PDF page 88), registered
as `milne-2017-algebraic-groups`. The original source is
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
The source pages and the complete official errata snapshot dated 2026-11-02
were read; those errata do not correct these two results.

The implemented proof is a derived argument specialized to finite algebras,
using derivations, translation of tangent vectors, and the Artinian
nilradical criterion. It does not formalize the full smoothness assertion of
Cartier's theorem or reproduce Milne's tensor argument. The general derivation
lemma and the dual-number helpers below are internal derived material.

## Implemented proof

First, `derivation_isNilpotent` proves that a `k`-derivation of a commutative
`k`-algebra preserves nilpotent elements in characteristic zero. The induction
is on a vanishing power of `a`. From `a^(n+1) = 0`, differentiation and
cancellation of the nonzero scalar `n+1` give `a^n * D(a) = 0`. For `n > 0`
this implies `(a * D(a))^n = 0`, so induction makes `D(a * D(a))` nilpotent.
The term `a * D(D(a))` is also nilpotent. The Leibniz rule identifies their
difference with `D(a)^2`, and nilpotence of this square gives nilpotence of
`D(a)`. The zero exponents are handled separately.

The dual-number helpers implement coefficient maps and the algebra map
`tangentLift φ d : H →ₐ[k] DualNumber k`, where `d` is a `k`-linear form
satisfying the Leibniz rule at a rational point `φ : H →ₐ[k] k`.
`exists_derivation_evaluating` then extends every such tangent form to a
derivation `D : Derivation k H H` satisfying `φ (D a) = d a`.

For this extension, write `F` for the dual-number point associated to `(φ,d)`.
Using convolution and the antipode, translate `F` by the inverse constant
point of `φ` to obtain a dual-number point `t` reducing to the identity.
Change coefficients from `k` to `H`, then multiply by the constant universal
point `id_H`. The resulting point `L : H →ₐ[k] DualNumber H` reduces to
`id_H` and evaluates under `φ` to `F`. Its second coefficient is the desired
derivation. Inverse identities are obtained by applying the point map to the
universal Hopf-algebra point and its antipode inverse; no convolution group
instance for arbitrary target algebras is assumed.

Consequently, `tangent_eq_zero_of_isNilpotent` shows that every tangent form at
`φ` kills every nilpotent element: the extended derivation preserves
nilpotents, and a field-valued algebra map kills them. The existing
`Langlands.GroupScheme.Lie.SubgroupEquality.exists_leibniz_ne_zero` separates
a nonzero class in `ker φ / (ker φ)^2` by such a tangent form. This proves
`nilradical_le_point_ker_sq`.

If `k` is algebraically closed and `H` is finite, every maximal ideal is the
kernel of a `k`-point. Indeed, its quotient is a finite extension field of `k`,
and `IsAlgClosed.lift` gives the required map into `k`. The ring `H` is
Artinian. The imported
`Langlands.ArtinianReducedCriterion.isReduced_of_nilradical_le_maximal_sq`
then proves `isReduced_of_isAlgClosed`: the nilradical lies in every maximal
ideal square, hence in its own square by the Artinian intersection formula;
a nilpotent idempotent ideal is zero.

Finally, `isReduced` extends scalars to `AlgebraicClosure k`. The tensor
product inherits the finite commutative Hopf-algebra structure, so the
algebraically closed case makes it reduced. The canonical map from `H` into
this tensor product is injective over a field. Reducedness descends along
this injection.

This module supplies the characteristic-zero reducedness input for the
finite-group-scheme exponent proof. It does not itself assert an exponent or
cover the positive-characteristic case.
