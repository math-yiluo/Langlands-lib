# Integral evaluation bounds and finite affine morphisms

This internal construction supplies the boundedness reflection used in
Kaletha–Prasad, Lemma 2.2.10 (2023, printed p.72 / PDF p.103). It uses the
published `IsAlgebraicallyBounded` predicate on actual global regular
functions and the actual identity-test rational points.

For a valuative field `F`, a commutative-ring map `f : A →+* B` and a family
`e : ι → B →+* F`, suppose each element of `A` has a nonzero uniform bound
under all the maps `e i ∘ f`. The construction `integralEvaluationBound`
assigns a nonzero uniform bound to the evaluations of any `b : B` integral
over `f`. The universes of `F`, `A`, `B` and `ι` are independent. Empty
evaluation families and zero or trivial source rings are allowed.

The implemented argument chooses a monic equation for `b`, and then a
common nonzero bound `c` for its finitely many coefficients, enlarged
valuatively to be at least one. A root cannot exceed `c`: otherwise the
leading monomial has strictly larger valuation than every lower monomial.
The nonarchimedean valuation of their sum equals that of the nonzero leading
monomial, contradicting the monic equation. The proof uses the canonical
representative `ValuativeRel.valuation F`; it makes no choice of a real-valued
norm and imposes no rank or nontriviality condition on the valuation.
`bounded_evaluations_of_integral` applies this construction to each element
when the whole ring map is integral.

For affine `F`-schemes `X` and `Y`, the theorem
`isAlgebraicallyBounded_of_integralHom` applies the construction to the actual
global-section pullback of an integral morphism `f : X ⟶ Y`.
The family consists of evaluation maps at the points of an arbitrary set
`S ⊆ X(F)`. Naturality of the published affine point equivalence identifies
evaluation after coordinate pullback with evaluation at the image point.
Bounds on `f(S)` therefore bound every regular function on `S`.

`isAlgebraicallyBounded_preimage_of_integralHom` specializes to an inverse
image of a bounded set in `Y(F)`. The finite-morphism corollary
`isAlgebraicallyBounded_preimage_of_finite` is the conclusion of KP Lemma
2.2.10. The formal result drops the finite-type hypotheses on the schemes:
integrality supplies a monic equation separately for every regular function,
so a finite generating family for the whole coordinate algebra is unnecessary.
It also replaces the standing Henselian-field setting by an arbitrary field
with `ValuativeRel`. The direct monic-equation proof justifies this extension.
There are no smoothness, reducedness, local-field or characteristic hypotheses.
Both schemes and their points are the existing relative scheme objects.

This unit supplies a transport construction, not the reductive spectral
criterion. The finite-kernel representation and the spectral bound on its
image remain separate obligations.

The source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Its 1 November 2024 corrections, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.24, amend the standing Henselian assumption and Lemma 2.2.5; those
restrictions are not needed by this elementary monic-equation argument.
