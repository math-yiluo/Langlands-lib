# Mixed-character chart data and overlap rigidity

The generic part of `Langlands.Algebra.MixedChartRing` defines
`Γ L = Multiplicative (AddAut L)` for a finite additive commutative
group `L` and its action on `W R A L` by algebra automorphisms. The
action convention twists the Hopf point by the inverse character
automorphism. Point evaluation commutes with change of coefficients
and determines the original algebra point injectively.

Fix `Λ = (r → ℤ) × F` and `Λ̄ = (r → ZMod m) × F`, with `r` and
`F` finite, `F` an additive commutative group and `m` nonzero.
`Datum R A r F m gen n` supplies a principal open `D(f)` of
`Spec (W R A Λ̄)` and a Hopf point into the group algebra of `Λ`
over that open. Its generator supports lie in the mixed box of
radius `n`; its scalar extension is surjective; and its reduction
is the universal point on `Λ̄`. It also supplies the rigidity bound,
the explicit condition that `m` annihilate `F`, a generating family
of `A`, and an invariant element `N` such that the translates of
`D(f)` cover `D(N)` on all prime ideals. These are data and proof
fields, not conclusions asserted for arbitrary inputs by this module.

For a datum `d`, `B` is the localization at `N`, and `actB` is the
localized action of `Γ Λ̄`, with an `R`-algebra version `actBAlg`.
At every field-valued point of `B`, a translate lies in `D(f)`.
The reduced universal point is consequently surjective there, so
twist freeness proves `actB_free` at all field-valued points.

`pushα` changes the coefficients of the extending mixed-character
Hopf point. Its Hopf equations, support bound, surjectivity and
reduction equation persist. If two local points differ by the group
action, `ker_pushα_eq` identifies the scalar-extended kernels of their
extensions. For a zero coefficient ring the statement is trivial;
otherwise surjectivity makes the supports generate `Λ`, and the
mixed-character rigidity theorem applies.

Conversely, equal scalar-extended kernels give a character
automorphism after localization at each maximal ideal, by the
published connected-base Hopf-point theorem. Since `m` annihilates
`F`, this automorphism descends to `Λ̄`. Injectivity of universal
point evaluation then proves `exists_act_of_ker_eq`, the local orbit
equation. This module does not identify points globally in one orbit.

This is an internal extension of the published torus chart ring
construction, reusing its generic group-algebra and scalar-extension
lemmas. No quotient scheme, descended group family, smoothness or
full chart-cover theorem is constructed here.
