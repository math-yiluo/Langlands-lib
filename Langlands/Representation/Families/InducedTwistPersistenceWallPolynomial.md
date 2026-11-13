# One polynomial for each rank-one wall

Author: Worker 5120.

This module proves the two lemmas that connect the genericity at one wall
(`InducedTwistPersistenceGenericity`) to the gallery induction
(`InducedTwistPersistenceGallery`). Both are in `Langlands.InducedTwistPersistence`.

## Jacquet modules of quotients

`isSubquotient_leviJacquet_quotient_of_injective`. Let `ι : I ↪ T` be an injective
morphism of smooth representations of `G(k)`, and `S` an invariant subspace of `I`. Then
for every actual parabolic `R` with rational Levi, `r_R(I/S)` is a subquotient of
`r_R(T)`. It is the quotient of `r_R(I)` by exactness on surjections
(`leviJacquet_map_surjective`). And `r_R(I) ↪ r_R(T)` by exactness on injections
(`leviJacquetFunctor_map_injective`).

## The wall polynomial

`exists_polynomial_wall_isIrreducible`. The data are:

- `G` connected reductive, `P = MN`, a parabolic `Q = LV` of `M`, and
  `j = lQ ≫ q ≫ l ≫ p`;
- a split component `a` of `M` with `b ≫ lQ ≫ q = a`, and a split component `b_L` of `L`;
- an actual parabolic `R₀` with `lR₀ ≫ r₀ = j`, and representatives `gW`, `φW` of
  `N_G(L)(k)/L(k)` relative to `R₀` (Renard V.4.3.3);
- an irreducible `σ` of `L(k)`, and twists `θ ψ` with `θ ψ (z) = ψ((lQ ≫ q) z)` for
  `ψ ∈ X(M)`, each `σ ⊗ θ ψ` supercuspidal with an exponent `χ0 ψ` of `b_L`;
- a family `Z ψ s` of representations of `G(k)` whose Jacquet module along every
  parabolic with Levi `j` is a subquotient of `r(i_{R₀}(σ ⊗ θ ψ))` (`hsub`);
- a wall `d : RationalRankOneWallData j F F'` with `b` not central in `d.M`, and a
  radical `v₁` of `d.Q`.

Assume Renard VI.8.5 (`GenericInducedIrreducibilityStatement.{u, max u v}`) and wall
twist surjectivity (`Plancherel.WallUnramifiedTwistSurjectivityStatement`). Then there
is a polynomial `g ≠ 0` on `X(M)` with the following property. Take `ψ` off its zero set,
any `s`, any irreducible `C` and any parabolic `R` with Levi `j`, such that `C ↪ r_R(Z ψ s)`
and `χ0 ψ` is an exponent of `C`. Then `i^{d.M}_{d.Q}(C)` is irreducible. This is
exactly the `hwall` input of `exists_polynomial_persistenceInvariant_of_gallery`.

## Proof

Wall surjectivity, applied to `P`, `Q` and the wall data, gives the surjection
`X(M) × X(d.M) → X(L)`. Here `d.levi_comp`, `d.proper` and `d.maximal` supply the
hypotheses, and `b` is the noncentral torus. For each representative `j`,
`exists_polynomial_isIrreducible_wall` with `f = lQ ≫ q` and the automorphism `φW j` gives
`g_j`. Take `g = ∏ g_j`; by `mem_rationalUnramifiedPrincipalOpen_prod`, `ψ` is off the
zero set of each `g_j`.

Given `C ↪ r_R(Z ψ s)`, `C` is a subquotient of `r_R(i_{R₀}(σ ⊗ θ ψ))`
(`IsSubrepresentation.isSubquotient`, `hsub`, `isSubquotient_trans`).
`pieces_of_supercuspidal_normalizer` gives two facts. That representation is
supercuspidal, so `C` is supercuspidal (`IsSupercuspidal.of_isSubquotient`). And `C` is
equivalent to the pullback of `σ ⊗ θ ψ` along some `φW j`. The conclusion of
`exists_polynomial_isIrreducible_wall` for that `j` then applies.

## Provenance and boundary

This is the wall polynomial of the derived second-adjointness route to Konno 2003,
Theorem 4.2. VI.8.5 and wall twist surjectivity enter only as the hypotheses `hVI` and
`hWS`. Both are published proof targets, not theorems.
