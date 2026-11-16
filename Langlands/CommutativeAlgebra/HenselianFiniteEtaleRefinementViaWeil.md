# Finite étale local refinement via Weil restriction

Authors: Worker 598 and Worker 607.

For an étale algebra `A` over a Henselian local commutative ring `R`, a prime
`q` of `A` above the maximal ideal of `R` gives a finite étale local
`R`-algebra `L` and an actual `R`-algebra map `A → L`. The theorem
`HenselianFiniteEtaleRefinement.exists_local_finite_etale_refinement_via_weil`
proves this without an additional Henselian inheritance premise.
`refinementOfPrimeViaWeil` chooses the result as `RefinementData R A`.
All carriers lie in the same arbitrary universe.

As in the imported conditional construction, put `K = κ(q)`. The residue
extension is finite because `A` is étale, so `K` is finite over `R`.
Localization and quotient preserve formal unramifiedness, and the kernel
calculation `ker(R → K) = 𝔪_R` proves that this map is local.
`CompleteLocal.exists_etaleCover` gives a local finite étale `R`-algebra `L`
and a surjection `π : L → K`.

Give `K` its `L`-algebra structure through `π`. The equality of the composite
`R → L → K` with the local structure map `R → K` shows that `R → L` is local.
The finite flat module `L` over the local ring `R` is free, hence projective.
The base-changed algebra `L ⊗[R] A` is étale, hence smooth, over `L`.
Its point with values in `K` comes from the original map `A → K`.

`HenselianFiniteEtaleResidueComparison.tensorResidueCoverEquiv` identifies
`K` with `L ⊗[R] κ(R)` as an `L`-algebra. Composing with the inverse gives a
point of `L ⊗[R] A` with values in that closed-fibre tensor product.
`HenselianSections.exists_lift_of_finite_projective_smooth` lifts this point
to an `L`-algebra map `L ⊗[R] A → L` by Henselian smooth lifting over `R`
after Weil restriction. Restricting scalars and composing with the right
tensor inclusion gives the required `A →ₐ[R] L`.

The provenance is internal: this is an explicit composition of the imported
finite étale cover, residue comparison, finite-projective smooth lifting,
and Mathlib base-change and finite-flat freeness results. It constructs the
algebraic refinement used in the affine scheme target. No prescribed residue
extension or preservation of the chosen prime under the resulting map is
claimed.
