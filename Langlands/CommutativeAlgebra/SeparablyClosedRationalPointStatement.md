# Rational points of geometrically reduced algebras over separably closed fields

`Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,v}` is a
Prop-valued statement. This module defines the proposition and proves nothing.

## Statement

Fix independent universes `u` and `v`. The proposition quantifies over:

- a field `k : Type u` with Mathlib's `[IsSepClosed k]` (separably closed);
- a commutative ring `R : Type v` with `[Algebra k R]`, Mathlib's
  `[Algebra.FiniteType k R]` (`R` is a finitely generated `k`-algebra) and
  `[Nontrivial R]` (so `R ≠ 0`);
- Mathlib's `[Algebra.IsGeometricallyReduced k R]`.

The conclusion is `Nonempty (R →ₐ[k] k)`: some `k`-algebra homomorphism `R → k`
exists. Geometrically, the nonempty affine `k`-scheme `Spec R` has a `k`-rational
point. A `k`-algebra map `R → k` is the same as a closed point `x` of `Spec R` with
`κ(x) = k`, namely the point given by its kernel.

There are no other hypotheses: `k` need not be perfect, and `R` need not be a
domain, smooth or of any fixed dimension.

## Convention for geometric reducedness

Mathlib's class `Algebra.IsGeometricallyReduced k R` asks that the base change of
`R` to an algebraic closure of each residue field of `k` is reduced. For a field `k`
the only prime ideal is `0`, and Mathlib's `Algebra.isGeometricallyReduced_field_iff`
shows the class is equivalent to `AlgebraicClosure k ⊗[k] R` being reduced.

The Stacks Project instead says that a `k`-scheme `X` is geometrically reduced if
every base change `X_{k'}` along a field extension `k'/k` has reduced local rings
(Definition 33.6.1, Tag 035V). For `X = Spec R` the two notions agree:

- In characteristic `p > 0`, Lemma 33.6.4 (Tag 035X) shows that `X` is geometrically
  reduced if and only if `X_{\bar k}` is reduced, where `\bar k` is an algebraic
  closure of `k`.
- In characteristic `0`, `k` is perfect. If `AlgebraicClosure k ⊗[k] R` is reduced,
  then so is its subring `R` (Mathlib's `Algebra.isReduced_of_isGeometricallyReduced`),
  and Lemma 33.6.3 (Tag 020I) shows that a reduced scheme over a perfect field is
  geometrically reduced. The converse is the case `k' = \bar k` of the definition.

These lemmas are in the registered snapshot
`stacks-geometrically-reduced-schemes-section-035u-2026-10-30` (file
`Stacks Project, Section 33.6 (Tag 035U)- geometrically reduced schemes.html`,
SHA256 `6435a4eaa6664fc49a44d8a086a01e582869c00f2377f660e077709e5df2f888`).
The comparison explains the hypothesis. It is not part of the Lean statement,
which uses Mathlib's definition as it is.

## Provenance

The proposition specializes two lemmas in the Stacks Project, Chapter 33
(Varieties), Section 33.25 (Schemes smooth over fields, Tag 04QM):

- Lemma 33.25.7 (Tag 056V): let `X` be a reduced scheme locally of finite type over a
  field `k`. Then `X` is geometrically reduced over `k` if and only if `X` contains a
  dense open which is smooth over `k`.
- Lemma 33.25.6 (Tag 056U): let `k` be a field. If `X` is smooth over `Spec(k)`, then
  the set of closed points `x ∈ X` with `κ(x)/k` finite separable is dense in `X`.

They are in the registered snapshot `stacks-schemes-smooth-over-fields-04qm-2026-11-03`
(fetched 2026-11-03, directory SHA256
`b0c10f669e8f60a9141294c5088a723370224f17745b8ba7e42298a2aeaf7a0f`), in the folder
`Stacks Project - Section 33.25 Schemes smooth over fields, Tags 04QM, 056U, 056V (HTML snapshot 2026-11-03)`:
`04QM.html` (section page, SHA256
`a2ca1cc791459393ec97ca9e1f48560723dcbec8822281f0338f5b58c72e8a4a`), `056U.html`
(SHA256 `cdb4e2d736b4753e039da647aceb1a4970b0b44b193da9ec285dd92f753d85d9`) and
`056V.html` (SHA256 `dea6682261dd2ffaf349ff96e2645cdebaad34e8a86792f968e02f89282890f2`).

How the statement follows from them. Take `X = Spec R`.

1. `X` is of finite type over `k` because `R` is a finitely generated `k`-algebra.
2. `X` is nonempty because `R ≠ 0`.
3. `X` is reduced because geometric reducedness implies reducedness
   (Mathlib's `Algebra.isReduced_of_isGeometricallyReduced`). By the convention
   comparison above, `X` is geometrically reduced in the Stacks sense.
4. By Tag 056V, `X` has a dense open `U` smooth over `k`. `U` is nonempty because
   `X` is nonempty.
5. By Tag 056U applied to `U`, some closed point `x` of `U` has `κ(x)/k` finite
   separable.
6. A finite separable extension of a separably closed field is trivial (Mathlib's
   `IsSepClosed.algebraMap_surjective`), so `κ(x) = k`. The composite of `R → κ(x)`
   with this identification is the required `k`-algebra homomorphism `R → k`.

The Stacks lemmas are about schemes. This statement specializes them to the affine
scheme `Spec R` of a finitely generated algebra, over a separably closed base field.
It asserts only that one rational point exists, not that rational points are dense.

## Context

This is a prerequisite for the proof task `151350b2-1913-480f-a828-3be21c0f5bd3`, whose
target is `Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteStatement`
(Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), Proposition
C.1.6). That proof works over a separable closure `k_s`. It needs `k_s`-rational
points of geometrically reduced `k_s`-schemes of finite type: the density of `G(k_s)`
in a smooth group `G`, and a `k_s`-point of a nonempty geometrically reduced locally
closed subscheme. This statement supplies that input in commutative-algebra form.
