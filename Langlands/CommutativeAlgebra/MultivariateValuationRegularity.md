# Regularity of finite-variable polynomial rings over valuation domains

Let `R : Type u` be a commutative ring. The entry construction
`polynomialVectorMonomialBasis σ n` combines the coordinate basis with
`MvPolynomial.basisMonomials` to give an `R`-basis of
`Fin n → MvPolynomial σ R`, indexed by `Σ _ : Fin n, σ →₀ ℕ`.
If the variable type `σ : Type v` is finite, this index is countable.
A finite free surjection therefore proves
`countablySpanned_of_finite_mvPolynomial`: any finite module over
`MvPolynomial σ R` with a compatible `R` action is countably spanned
as an `R`-module. The module may lie in an independent universe `w`.

`mvPolynomialAction_hasProjectiveDimensionLE` proves that a compatible
polynomial action in `k` variables raises a coefficient-ring
projective-dimension bound `d` by at most `k`. The module is in universe
`w`, and this theorem assumes `Small.{w} R`. For zero variables the proof
uses the actual algebra equivalence with `R` and the identity semilinear
equivalence on the module. At a successor, `MvPolynomial.finSuccEquiv`
identifies the ring with a univariate polynomial ring over the preceding
polynomial ring. The action is restricted through that equivalence,
the induction hypothesis gives coefficient dimension at most `d + k`,
and the imported polynomial-action exact-sequence bound raises it by
one. The identity semilinear equivalence transports the result back to
the original ring action. The necessary smallness of the univariate
polynomial ring follows from the same algebra equivalence.

`mvPolynomialAction_hasProjectiveDimensionLE_of_finite` renames any
finite variable type using `Finite.equivFin`. It proves the bound
`d + Nat.card σ`, with the same size assumption on `R` and no chosen
enumeration in its statement. The transported coefficient action is
compatible with the original `R` action by the algebra-equivalence
commutation law.

Now assume that `R` is a valuation domain, with arbitrary rank and
fields allowed. A finite `MvPolynomial σ R`-module that is torsion-free
over `R` is countably spanned over `R`, so the imported valuation
exhaustion theorem bounds its coefficient-ring projective dimension by
one. The finite-variable action theorem yields
`hasProjectiveDimensionLE_of_finite_mvPolynomial_of_valuationRing`,
whose bound is `1 + Nat.card σ`. Its module universe is independent,
subject to `Small.{w} R`.

For a finitely presented polynomial module `M` in universe `max u v`,
choose a finite free polynomial surjection. Finite presentation makes
its relation kernel finite over the polynomial ring. This kernel is
torsion-free over `R` as a submodule of a finite free polynomial module,
so its polynomial dimension is at most `1 + Nat.card σ`. The actual
kernel short exact sequence, with projective middle term, proves
`hasProjectiveDimensionLE_of_finitePresentation_mvPolynomial_of_valuationRing`
with bound `1 + Nat.card σ + 1`. No optimality is claimed. This proves
`finiteProjectiveDimensionForFinitelyPresentedModules_mvPolynomial_of_valuationRing`
for every finite variable type, in its independent universe.

Combining that result with the imported
`finiteFreeSubmoduleCoherent_mvPolynomial_of_valuationRing` proves
`finitelyPresentedRegularRing_mvPolynomial_of_valuationRing`.
The predicate `FinitelyPresentedRegularRing` asserts finite presentation
of each finitely generated submodule of a finite free module, together
with finite projective dimension of every finitely presented module.
The imported localization permanence theorem gives
`finitelyPresentedRegularRing_mvPolynomial_localization_of_valuationRing`
for every submonoid, including one containing zero.

This is an internal derivation from the explicit coordinate-monomial
basis, Mathlib algebra equivalences and projective-dimension transport,
and the imported countable valuation, polynomial-action, coherence and
localization results. It does not establish permanence for smooth or
étale algebras, or any geometric line-bundle extension statement.
