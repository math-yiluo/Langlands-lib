# The Hecke bimodule and the functors P and pseudo-F

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.1, printed p.70 / PDF p.76, using
II.3.7 Proposition (ii), printed p.47 / PDF p.53, and the functors of
I.2.3, printed pp.17–18 / PDF pp.23–24. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The groups are Hausdorff locally compact nonarchimedean groups, with left
Haar measures and a continuous homomorphism `φ : H →* G`. Group and
representation-carrier universes remain independent.

Let `J` denote `haarInversion` and `Δ` denote `haarScale`; Renard's
modular function is `δ = Δ⁻¹`. The right regular representation on
Haar distributions is obtained by conjugating the left regular representation
by `J`. Its explicit function formula is

`r(h)f(x) = Δ(φ(h)⁻¹) f(xφ(h))`.

`rightModule` acts by
`f · a = JG(JH(a) · JG(f))`, using the actual left Hecke action of
`HomomorphismLeft`. Its laws follow from the anti-multiplicativity and
involutivity of `J`, and its nondegeneracy from that of the left action.
`rightModule_eq_integrated` verifies that this is precisely the integrated
right regular representation evaluated at `JH(a)`, as prescribed in III.2.1.
There is no unimodularity restriction.

The right subgroup action commutes with left multiplication by `H(G)`,
by applying `J` to the already proved left-action/right-multiplication
commutation. The two subgroup actions commute by a local-unit argument
on the original Hecke algebra: for a left multiplier `L`, right multiplier
`R`, and vector `f`, choose a common left unit `e` for `f` and `R(f)`;
then `L(R(f)) = L(e) R(f) = R(L(e) f) = R(L(f))`.
Thus `bimodule` and `bimodule_isNondegenerate` give the specified
two-sided nondegenerate `H(H)` bimodule on `H(G)`.

`P` and `pseudoF` are direct specializations of the published
`NondegenerateTensorFunctor.P` and `RenardHomFunctors.pseudoF`, with the
right action just constructed and ordinary left multiplication by `H(G)`.
Together with `HomomorphismLeft.F/I` these are all four Hecke-side functors
of III.2.1. Their targets use the original additive module convention
of Chapter I, and their output universe is `max uG v`.

This definition unit does not assert their adjunctions or their comparisons
with functors on smooth representations; those are subsequent proposition
targets.
