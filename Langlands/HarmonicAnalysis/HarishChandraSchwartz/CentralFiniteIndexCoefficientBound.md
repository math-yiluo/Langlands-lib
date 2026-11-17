# Extending coefficient Xi bounds across a finite central quotient

This module is internal glue for the coefficient input in the wave-packet
estimates. It combines published group quotient, unitary central-character,
Xi translation and rational square-integrable decay results. No additional
original-literature assertion is made. All declarations are in
`Langlands.HarishChandraSchwartz`.

The generic setting consists of a group `G` with a topology, a complex
representation `ρ` on a carrier in an independent universe, a prescribed
`UnitaryCentralCharacter ρ`, normal subgroups `N` and `A`, and an inclusion
`A ≤ center G`. The quotient `G / (N ⊔ A)` is finite. The weight `Ξ` is
nonnegative, invariant under right multiplication by `A`, and satisfies the
existing `UniformTranslationBound Ξ`: for each fixed pair of translating
points, one real constant bounds the translated weight by the original one.
No local compactness or continuity of the weight is needed for this algebraic
extension.

`hasXiBoundedCoefficients_of_finite_central_quotient` assumes that for every
vector and smooth functional there is a real Xi bound on the subgroup `N`.
It proves the existing `HasXiBoundedCoefficients Ξ ρ` on all of `G`, with a
strictly positive constant for each coefficient. The argument chooses one
representative `t j` of each of the finitely many quotient classes. For the
coefficient of `v`, apply the subgroup bound to `ρ(t j)v`. Every `g` can be
written `n * t j * a` with `n ∈ N` and `a ∈ A`: the quotient representative
formula, the normal-subgroup product formula for `N ⊔ A`, and normality of
`N` give this order of factors. The prescribed unitary central character
removes `a` from the coefficient norm. Translation by `(t j)⁻¹` and invariance
under `A` bound `Ξ(n)` by `max(D j, 0) * Ξ(g)`.
If `C j` are the subgroup constants, the global constant is
`1 + sum j, max(C j, 0) * max(D j, 0)`. Nonnegativity of `Ξ` justifies
increasing the constants, and the sum makes the bound uniform over the
finitely many classes.

`finiteCentralCoefficientConstant` selects a constant from this result for
each original vector and smooth functional.
`finiteCentralCoefficientConstant_spec` states its strict positivity and
its bound on the original coefficient at every group point.
`hasXiBoundedCoefficients_of_rapid_on_finite_central_quotient` supplies the
subgroup assumption by applying the existing
`HasRapidlyDecreasingCoefficientsOn` to order zero. Its height function is
arbitrary because the order-zero power equals one; no height estimate enters
this extension.

On actual rational points,
`hasXiBoundedCoefficients_of_rationalNormKernel` uses the original explicit
finite-index premise for `RenardCartan.splitValuationImage s`. The published
`finite_rationalCentralQuotient` identifies its consequence as finiteness of
`G(F) / (G(F)¹ ⊔ image(s(F)))`. The published central Xi invariance and uniform
translation bound provide the generic weight assumptions. Thus rapid decay
on the actual rational norm kernel, together with a prescribed unitary central
character, implies a global bound by the actual `rationalXi hKc hPK`.
Here `s` is any central group-scheme map with the given finite-index premise;
it need not be asserted to be a split component for this step.

Finally, `hasXiBoundedCoefficients_of_rationalSquareIntegrable` applies the
published `hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable` from
`RationalSquareIntegrableDecayProof`. Its actual split component, quotient
Haar measure, and square-integrability data are unchanged. Square
integrability supplies the unitary central character. A matrix representation
on any nonempty finite index type supplies the height used by the rapid-decay
helper; no closed-immersion premise is needed by that helper or by the
order-zero extension. The field and representation-carrier universes remain
independent.

The last result explicitly retains the rapid-decay proof's structural
premises `SimultaneousStandardBasisAt` and `FiniteCartanCovering` for a compact
subgroup `K0`. The module does not prove existence of that structural package,
transport the global Xi estimate to a nested actual Levi, or prove a full
Schwartz wave-packet bound. In particular it does not complete or modify the
source-normalized joint and component VI.3.1 targets.
