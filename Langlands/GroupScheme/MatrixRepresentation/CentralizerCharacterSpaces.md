# Character spaces of a commutative subgroup are stable under its centralizer

Author: Worker 5662.

This module proves a standard fact on all affine tests. Let `T` be a commutative group
scheme mapping to `G` by `i`, and let `f : H ⟶ G` take values in the all-test
centralizer of `i`. Then the restriction of a representation of `G` to `H` preserves
every character space of its restriction to `T`. Module `Reductive/SplitLeviIsotypicWeights`
uses it with `T` a base-changed split torus `S` and `H` the base change of the derived
group of its centralizer, for instance the actual anisotropic kernel. There the
`S`-isotypic parts of a representation of `G_K` become representations of that derived
group. This is the first step of the comparison of Tits obstructions with the anisotropic
kernel (Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), §3.4 and §5.5).

The base field `k` is arbitrary. No smoothness, reducedness or characteristic assumption
is made, and stability is the published all-affine-test notion `IsStableSubspace`.

## The tensor functional

- `tensorFunctional R A ℓ` is the `R`-linear map `id_R ⊗ ℓ : R ⊗[k] A → R` for a
  `k`-linear functional `ℓ : A → k`. It is built from Mathlib's
  `TensorProduct.AlgebraTensorModule.map` and `TensorProduct.AlgebraTensorModule.rid`.
- `tensorFunctional_tmul`: it sends `r ⊗ a` to `ℓ(a) • r`.
- `tensorFunctional_includeRight`: it sends `1 ⊗ a` to `ℓ(a)`, viewed in `R`.
- `tensorFunctional_includeLeft_mul`: it is `R`-linear for left multiplication by
  `r ⊗ 1`.
- `tensorFunctional_map_includeLeft_mulVec`: applied entrywise, it commutes with a matrix
  over `R` acting through `r ↦ r ⊗ 1`.

## Centralizer stability

`isStableSubspace_characterSpace_of_centralizes i f hf ρ χ` has the hypothesis
`hf : SubgroupFunctor.range f ≤ torusCentralizer i`: on every test scheme, the points of
`G` of the form `h ≫ f` lie in the all-test centralizer of `i`. The conclusion is that the
published character space `(ρ.restrict i).characterSpace χ` is a stable subspace for
`ρ.restrict f`.

Proof. Fix an affine test algebra `A`, a point `x` of `H` over `A`, a character vector `v`
and a functional `ℓ : A → k`. Stability requires that the vector `w` with
coordinates `ℓ((ρ(f x) v)_r)` is again a `χ`-vector. By the published universal
criterion `mem_characterSpace_iff`, it is enough to check the character equation at
the universal point `s` of `T` over its coordinate algebra `R`. Pass to the test algebra
`R ⊗[k] A` with the two points `s ⊗ 1` and `1 ⊗ x`. The centralizer hypothesis, applied
with the refinement `Spec(R ⊗ A) → Spec A`, says that `f(1 ⊗ x)` and `i(s ⊗ 1)` commute.
So their matrices commute (`affineMatrix_naturality` identifies them with the images of
the matrices of `f x` and `i s`). Apply `id_R ⊗ ℓ` to the vector
`ρ(i s) ρ(f x) v = ρ(f x) ρ(i s) v = ρ(f x) χ(s) v`. The left side gives
`ρ(i s) w`, the right side gives `χ(s) w`, and this is the character equation.

`range_comp_le_torusCentralizer`: if `j : M ⟶ G` represents the centralizer of `i`
(`IsRepresentedBy`), then `range (g ≫ j) ≤ torusCentralizer i` for every `g : H ⟶ M`.

`range_le_torusCentralizer_baseChange`: the hypothesis `range f ≤ torusCentralizer i` is
preserved by base change along any field extension `K/k`. The proof rewrites with the
published `range_baseChangeHom` and `torusCentralizer_baseChange` and uses the definition
`mem_baseChange` of the base-changed subgroup functor.

The provenance is internal: the module combines published Library results (the
all-test centralizer, its base change, the universal character criterion and
`affineMatrix_naturality`) with Mathlib's tensor products. It uses no external theorem.
