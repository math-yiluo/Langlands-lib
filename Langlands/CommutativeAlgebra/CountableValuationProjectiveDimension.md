# Countable spanning families and valuation-ring polynomial dimension

Let `R` be a commutative ring in universe `u` and `M` an `R`-module in
an independent universe `v`. `CountablySpanned R M` means that there
exists `g : ℕ → M` whose range spans `M`. The entry definition
`finiteGeneratorSpan g n` is the span of the first `n` members of `g`.
It is finitely generated, is monotone in `n`, and its supremum is the
span of the whole range. Thus a spanning sequence gives an exhaustion.

A countable spanning set supplies such a sequence: insert zero to make
the set nonempty, enumerate it, and observe that insertion of zero
preserves the spanning property. A basis with countable index set
therefore gives `CountablySpanned`. The property passes through a
surjective linear map by mapping the spanning sequence.

For a valuation domain `R` and torsion-free `M`, each finite prefix span
is finitely generated and torsion-free. The imported theorem
`free_of_finite_of_isTorsionFree_of_valuationRing` makes it free and
hence projective. Applying the actual telescope resolution proves
`hasProjectiveDimensionLE_one_of_countablySpanned_of_valuationRing`:
the categorical projective dimension of `ModuleCat.of R M` is at most
one. There is no rank, Noetherian, or nonfield restriction on the
valuation domain, and the module universe remains independent.

If `M` has a compatible `R[X]`-module structure and is finite over
`R[X]`, a finite free polynomial module surjects onto `M`. The monomial
basis of `R[X]`, combined with the finite coordinate index, gives a
countable `R`-basis of that source. Restricting the surjection to `R`
proves `countablySpanned_of_finite_polynomial` for every commutative
coefficient ring.

For a valuation domain, if such a finite polynomial module is also
torsion-free over `R`, its underlying `R`-dimension is at most one by
the preceding exhaustion. The imported polynomial-action dimension
bound gives
`hasProjectiveDimensionLE_two_of_finite_polynomial_of_valuationRing`.
This theorem assumes `Small.{v} R`, as required by the polynomial
induction functor's projective-object argument. It permits independent
ring and module universes subject to that explicit size assumption.

For a finitely presented `R[X]`-module `M` in universe `u`, choose a
finite free surjection onto `M`. Its kernel is finite over `R[X]` by
finite presentation. As a submodule of the finite free polynomial
module, the kernel is torsion-free over `R`; the preceding result
therefore gives kernel dimension at most two. The source is
projective, and the actual kernel short exact sequence gives
`hasProjectiveDimensionLE_three_of_finitePresentation_polynomial_of_valuationRing`.
In particular,
`finiteProjectiveDimensionForFinitelyPresentedModules_polynomial_of_valuationRing`
proves the Library's finite-projective-dimension predicate for `R[X]`.
The bound three is the bound proved here; no optimality claim is made.

This is an internal derivation from explicit spanning constructions,
Mathlib's monomial basis and finite-presentation kernel theorem, and
the imported valuation freeness, telescope, and polynomial-action
results. It asserts no coherence of `R[X]`, no permanence for more
general algebras, and no line-bundle extension theorem.
