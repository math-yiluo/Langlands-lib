# Galois descent of cocharacter data

Module `Langlands.GroupScheme.Torus.CocharacterGaloisDescent`, namespace
`Langlands.GroupScheme.CocharacterDatum`. It imports Worker 1001's
`Langlands.GroupScheme.Torus.CocharacterDatum` and
`Langlands.GroupScheme.Torus.CocharacterCoefficientDescent`.

Setting: `k` is a field, `N` a finite field extension of `k`, `Z` a commutative
group scheme over `Spec k`, and `Λ` an additive commutative group. Points of
`Z` with coefficients in a `k`-algebra `S` are the `Lie.AffinePoints Z.toGrp S`.
For a `k`-algebra map `f : S →ₐ[k] S'`, `coeffMap f` sends points over `S[Λ]`
to points over `S'[Λ]` by applying `f` to coefficients. `IsDatum χ m p` (from
`CocharacterDatum`) says that the point `p` over `S[Λ]` is multiplicative and
that the character `χ` takes the value `X^m` on it.

## Definitions

- `galoisNorm k p`. For a point `p` over `N[Λ]`, it is the product
  `∏ σ, coeffMap σ p` over all `σ : N ≃ₐ[k] N`, taken in the commutative group
  of points of `Z` over `N[Λ]`.

## Statements

- `mapAlgHom_comp_mapAlgHom_algEquiv`, `coeffMap_coeffMap_algEquiv`. For
  `τ, σ : N ≃ₐ[k] N`, applying the coefficient maps of `σ` and then `τ` is the
  coefficient map of `τ * σ`, both on `N[Λ]` and on points over `N[Λ]`.
- `coeffMap_galoisNorm`. `coeffMap τ (galoisNorm k p) = galoisNorm k p` for
  every `τ : N ≃ₐ[k] N`.
- `coord_galoisNorm_mem`. Assume `N / k` is Galois and `Z` is affine. Then
  every value of the coordinate algebra map of `galoisNorm k p` lies in the
  image of `mapAlgHom Λ (Algebra.ofId k N) : k[Λ] → N[Λ]`.
- `IsDatum.exists_of_isGalois` (Galois descent). Assume `N / k` is finite
  Galois and `Z` is affine. If `p` is a cocharacter datum of weight `m` over
  `N[Λ]` for `χ`, then some point `p'` over `k[Λ]` is a cocharacter datum for
  `χ` of weight `Nat.card (N ≃ₐ[k] N) • m`.

## Proofs

1. Composition. Both sides act on the `γ`-coefficient as `τ ∘ σ`. On points,
   this is the identity `affineMap (g ∘ f) = affineMap g ∘ affineMap f`
   (`Lie.affineMap_comp`).
2. Invariance. `coeffMap τ` is a group homomorphism, so it maps the product to
   `∏ σ, coeffMap (τ * σ) p` by step 1. Reindexing along the bijection
   `σ ↦ τ * σ` of the Galois group gives the original product.
3. Coordinates. By `coord_affineMap`, the coordinate map of `coeffMap σ ν` is
   that of `ν` followed by `mapAlgHom Λ σ`. With `ν = galoisNorm k p`, step 2
   shows that each coordinate value of `ν` is fixed by `mapAlgHom Λ σ` for
   every `σ`. Galois descent of coefficients
   (`exists_mapAlgHom_ofId_eq_of_isGalois`) puts it in the image of `k[Λ]`.
4. Descent of the datum. Each conjugate `coeffMap σ p` is a datum of weight
   `m` (`IsDatum.coeff_map`), so their product `ν` is a datum of weight
   `∑ σ, m = Nat.card (N ≃ₐ[k] N) • m` (`IsDatum.prod`). The map
   `f = mapAlgHom Λ (Algebra.ofId k N)` is injective because `k → N` is
   injective (`mapAlgHom_injective`). By step 3 and `exists_affineMap_eq`,
   `ν = coeffMap (Algebra.ofId k N) p'` for some point `p'` over `k[Λ]`.
   Finally, `IsDatum.of_coeff_map` turns the datum `ν` back into a datum `p'`
   of the same weight over `k[Λ]`.

## Provenance

This is the norm argument of Galois descent: a product over all Galois
conjugates is Galois invariant, and Galois-invariant coordinates are rational.
The statement and route were specified by Worker 1001 for torus cocharacter
detection (task 6d0882ee), and the Lean code uses their `CocharacterDatum` API.
It is a derived internal step, not quoted from a source. Torus cocharacter
detection uses it to bring a cocharacter defined over a Galois splitting field
down to the base field. The weight is multiplied by the positive integer
`Nat.card (N ≃ₐ[k] N)`, so a nonzero weight stays nonzero when `Λ` is
torsion-free.
