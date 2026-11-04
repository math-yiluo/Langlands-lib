# Coefficients along a linearly independent family on a product

Author: Worker 1412.

This module is an internal helper for the proof of
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(see [AffineFiniteTypeCocycleModelProof](../GroupScheme/AutomorphicAction/AffineFiniteTypeCocycleModelProof.md)).
It proves a uniqueness statement for expansions of global functions on a product
`X ×_k T`, where `X` is affine over a field `k` and `T` is arbitrary. The content is
standard: over a field, `Γ(X) ⊗_k Γ(V) → Γ(X ×_k V)` is an isomorphism for affine `V`,
and tensors over a field have unique coefficients along a linearly independent
family. No literature claim is formalized.

All declarations are in `Langlands.AlgebraicGeometry.ProductCoefficients`, for a field
`k : Type u`.

## Linear algebra

- `exists_dual`: for a `k`-module `M`, a linearly independent family
  `e : ι → M` with `DecidableEq ι`, and an index `j`, there is a `k`-linear functional
  `f : M →ₗ[k] k` with `f (e l) = 1` for `l = j` and `0` otherwise.
- `coeff_eq_zero_of_sum_tmul_eq_zero`: for `k`-modules `M`, `N`, a finite index type
  `ι`, a linearly independent `e : ι → M` and `n : ι → N`, if
  `∑ l, e l ⊗ₜ[k] n l = 0` in `M ⊗[k] N`, then `n j = 0` for every `j`.

`exists_dual` takes the coordinate functional `j` of the basis
`Module.Basis.span he` of the span of `e` and extends it to `M` with
`LinearMap.exists_extend` (possible over a field). Its values on `e l` are those of the
basis coordinate on the basis vector `l`. For `coeff_eq_zero_of_sum_tmul_eq_zero`,
apply `f.rTensor N` followed by `TensorProduct.lid k N` to the vanishing sum. The
result is `∑ l, f (e l) • n l = n j`, so `n j = 0`.

## Coefficients on a product

`coefficients_injective`: let `X T : Over (Spec (CommRingCat.of k))` with `X.hom`
affine (`IsAffineHom X.hom`), and nothing assumed of `T`. Let `ι` be a finite type and
`e : ι → Γ(X.left, ⊤)` be linearly independent over `k`. Here `Γ(X.left, ⊤)` carries the
`k`-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤` from the
Library, given by pullback along the structure morphism. If `y y' : ι → Γ(T.left, ⊤)`
satisfy

`∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (y l) =
  ∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (y' l)`

in the global functions of the product `X ⊗ T` (the scheme pullback over `Spec k`),
then `y = y'`.

Proof. Put `d l = y l - y' l`. The hypothesis says
`∑ l, fst^*(e l) * snd^*(d l) = 0`. Fix an affine open `V` of `T`. The Library
theorem
`P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.solution`
(applied to `X.hom`, `T.hom`, the affine open `⊤` of the affine scheme `X`, and `V`)
gives a `k`-algebra isomorphism
`φ : Γ(X, ⊤) ⊗[k] Γ(T, V) ≃ Γ(X ×_k T, fst⁻¹ ⊤ ⊓ snd⁻¹ V)` with
`φ (a ⊗ₜ b) = fst^* a * snd^* b`. Restrict the vanishing sum to
`fst⁻¹ ⊤ ⊓ snd⁻¹ V`. Using `Scheme.Hom.map_appLE` to identify the restricted pullbacks
with the `appLE` maps in the formula for `φ`, it becomes the image under `φ` of
`∑ l, e l ⊗ₜ (d l)|_V`. Injectivity of `φ` makes that tensor zero, and
`coeff_eq_zero_of_sum_tmul_eq_zero` gives `(d j)|_V = 0` for all `j`.
Finally, a global function on `T` whose restriction to every affine open vanishes is
zero. Every point has an affine open neighbourhood
(`exists_isAffineOpen_mem_and_subset`), so all germs of `d j` vanish, and
`TopCat.Presheaf.section_ext` for the structure sheaf gives `d j = 0`.
