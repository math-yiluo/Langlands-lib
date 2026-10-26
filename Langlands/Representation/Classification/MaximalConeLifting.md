# Lifting opposite exponents of a twisted Jacquet quotient

Author: Worker 23.

This module is an internal helper for the proof of
`Langlands.GLMaximalConeJacquetQuotientStatement` (task b291a31b). Let `S` be a
quotient of the normalized opposite Jacquet module of `A` along `C`. The target
statement asks for temperedness of the real twist `T.leviRealPowerTwist C (-t) S.ρ`.
The published dual-opposite tempered sufficiency criterion
(`Langlands.GLProductLeviDualOppositeTemperedSufficiencyStatement`) tests that
twist along every refinement `D` of `C`. This module turns each such test datum
into a dual exponent of `A` along the flattened shape `C.flatten D`. This is the
step `e^λ χ ∈ Exp(τ_λ, P̄') ⊂ Exp(π_{P̄'})` in Konno 2003, proof of
Theorem 3.5(i), p.397, carried out for the Library's normalizations.

## Flattened block coordinates

In namespace `Langlands.GeneralLinear.BlockShape`, for `D : BlockRefinement C`:

- `flattenOuter C D k`: the outer block `((C.flattenBlockEquiv D).symm k).1` of a
  flattened block. `flattenOuter_flattenBlockEquiv` (simp) evaluates it.
- `flattenBlockEquiv_le_iff`: inside one outer block `j`, the flattened order is
  the inner order, by the published `flattenBlockEquiv_lt_iff`.
- `flattenOuter_mono`: `flattenOuter` is monotone.
- `sum_filter_flattenOuter`: the sum over flattened blocks with outer block `j` is
  the sum over the inner blocks of `D j`.
- `size_eq_sum_flattenOuter`: `C.size j` is the sum of the flattened sizes over
  that fibre (published `flatten_size_flattenBlockEquiv` and `(D j).sum_eq`). So
  `flattenOuter` is a consecutive coarsening in the sense of the target statement.
- `sum_filter_flattenOuter_le`: a partial sum over the flattened blocks
  `k ≤ (j, i)` in the fibre of `j` is the inner partial sum over `i' ≤ i`.
- `flattenedLeviEquiv_blockScalarLevi_comp R a`: the flattened block scalar of
  `a ∘ flattenOuter` corresponds, in the outer Levi, to the outer block scalar of
  `a`. Both have the same ambient matrix (`flattenedLeviEquiv_embedding` and
  `leviEmbedding_blockScalarLevi_coarsen` of module `MaximalConeExponents`), and
  the outer Levi embedding is injective (published `leviEmbedding_injective`).

## Opposite Jacquet classes

In namespace `Langlands.PadicField.TopologicalData`:

- `oppositeJacquetMk T C A`: the published coinvariant map `Jacquet.mk`, typed with
  the bundled `CuspidalJacquetMultiplicity.oppositeJacquet T C A` as target.
  `oppositeJacquetMk_surjective` and `oppositeJacquetMk_apply_of_mem` (invariance
  under the opposite radical) follow from `Jacquet.mk_surjective` and
  `Jacquet.mk_apply_subgroup`.
- `oppositeJacquet_mk`: `J.ρ m (mk v) = δ_C^{1/2}(m) • mk (A.ρ (leviEmbedding m) v)`,
  with `δ_C^{1/2} = T.leviHalfModulus C`. The bundled action uses the inverse of
  the upper modulus, whose inverse half is the positive half. The proof unfolds
  the definition as in the published transitivity proof.

## The refined opposite radical

- `Langlands.Parabolic.OppositeTransitivity.lower_determinant_one`: an element
  of an opposite block radical has determinant one. The block-triangular
  determinant has identity diagonal blocks. This module reuses the existing
  proof, exposed as a public lemma in
  `Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof`.
- `mem_normOneLevi_of_mem_refinedOppositeUnipotent`: hence the refined opposite
  radical `refinedOppositeUnipotent F C D` lies in `T.normOneLevi C`.
- `leviHalfModulus_of_mem_refinedOppositeUnipotent` and
  `leviRealPowerCharacter_of_mem_refinedOppositeUnipotent`: the outer half modulus
  and every real determinant character are trivial on it (published
  `normOneLevi_le_ker_leviModulus`, `normOneLevi_le_ker_leviRealPowerCharacter`).

## Characters along a flattening

- `leviHalfModulus_flatten`: for `m` in the flattened Levi, with
  `x = flattenedLeviEquiv F C D m`,
  `δ_{flat}^{1/2}(m) = δ_C^{1/2}(x) · δ_D^{1/2}(x)`, where `δ_D^{1/2}` is the
  published `refinedLeviHalfModulus`. This combines the published
  `composedLeviModulus_flattened` and `composedLeviHalfModulus_eq`. The outer
  factor is definitionally `leviHalfModulus C` of `x`.
- `leviRealPowerCharacter_flatten`: the coarse real determinant character with
  exponents `t` at `x` equals the flattened real determinant character with
  exponents `t ∘ flattenOuter` at `m`. This is the first clause of the published
  `refinedLeviRealTwist`, applied at the section of `x` (instantiated with a
  trivial representation, since the clause does not involve it).
- `isRealPartOf_mul_leviRealPowerCharacter`: if `s` is a real part of `ψ`, then
  `ψ · (c_u ∘ blockScalarLevi)` has real part `s + size · u`. This uses the
  published `coe_leviRealPowerCharacter_blockScalar` and `Real.rpow_add`.

## The lifting theorem

`isDualJacquetExponent_flatten_of_quotient f hf t hψ hφ heig`. The inputs are:

- a surjective intertwiner `f` from the opposite Jacquet module of `A` along `C`
  onto `S.ρ`;
- a real vector `t` and a character `ψ` of the flattened split centre with open
  kernel;
- a nonzero `φ` on `RefinedOppositeJacquetModule C D σ`, where
  `σ = T.leviRealPowerTwist C (-t) S.ρ`, with
  `φ (N(x_a) (mk_D v)) = ψ a · φ (mk_D v)`. Here `N` is the published
  `normalizedRefinedOppositeJacquet` and `x_a` is the flattened block scalar of
  `a` (exactly the hypothesis form of the tempered sufficiency criterion).

Conclusion: `T.IsDualJacquetExponent (C.flatten D) A χ'` with
`χ' = ψ · (c^{flat}_{t ∘ flattenOuter} ∘ blockScalarLevi)`.

Proof, via the source criterion `isDualJacquetExponent_iff` (module
`MaximalConeExponents`) with `ℓ = φ ∘ mk_D ∘ f ∘ mk_C`:

1. **Open kernel.** The kernel of `χ'` contains the kernels of `ψ` and of the
   real determinant character on block scalars. The latter is open because the
   block-scalar map is continuous and the character has open kernel.
2. **Nonzero.** `ℓ ≠ 0`, because `mk_D`, `f` and `mk_C` are surjective.
3. **Invariance.** By the published `flattenedOppositeUnipotentComparison`, the
   flattened opposite radical is the composed radical: elements `g` of the outer
   opposite parabolic whose Levi projection `m` lies in the refined opposite
   radical. Write `g = u · leviEmbedding m` with `u` in the outer radical
   (`oppositeDecomposition`). Then `u` is killed by `mk_C`. The half modulus and
   the twist are trivial at `m`, so `m` acts through `f` and `σ`, and `mk_D`
   kills it.
4. **Eigen-equation.** The flattened block scalar of `a` is
   `leviEmbedding_C x` (`flattenedLeviEquiv_embedding`). Moving it through `mk_C`
   (factor `δ_C^{-1/2}(x)`), `f`, the twist (factor `c_t(x)`) and `mk_D` (factor
   `δ_D^{-1/2}(x)`), the hypothesis yields
   `ℓ(A(x) w) = δ_C^{-1/2} δ_D^{-1/2} c_t(x) ψ(a) ℓ(w)`. By the two character
   identities above this is `δ_{flat}^{-1/2}(a) χ'(a) ℓ(w)`.

## Zero outer totals

- `refinedLeviHalfModulus_blockScalarLevi_comp`: the refined half modulus is
  trivial at outer block scalars. By `leviHalfModulus_flatten` the flattened half
  modulus is the outer half modulus times the refined one. By
  `leviModulus_blockScalarLevi_coarsen` (module `MaximalConeExponents`) the
  flattened and outer moduli agree on outer block scalars.
- `sum_fibre_eq_zero_of_unitary σ hω hunit hφ heig hs j`. Suppose the outer block
  scalars act on `σ` by a character `ω` of norm one, and `φ ≠ 0` is a
  `ψ`-eigenfunctional on a refined opposite Jacquet module of `σ`, as above, with
  `ψ` of real part `s`. Then `∑_{flattenOuter k = j} s k = 0`. Evaluating the
  eigen-equation at `a ∘ flattenOuter` on a vector `v` with `φ (mk_D v) ≠ 0`
  gives `ψ (a ∘ flattenOuter) = ω a`. So the fibre sums of `s` are a real part
  of `ω` (`isRealPartOf_coarsen`), and so is `0`, because `‖ω‖ = 1`. Real parts
  are unique.

## Sources

T. Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups* (2003), registered as
`konno-2003-langlands-classification`, proof of Theorem 3.5(i), p.397: exponents
of `τ_λ` along smaller parabolics are exponents of `π`. The Lean statement is a
derived internal helper for the Library's opposite normalization, proved
directly.
