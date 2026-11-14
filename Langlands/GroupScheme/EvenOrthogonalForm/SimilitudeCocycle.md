# The similitudes of the Galois twists form a cocycle up to scalars

Let `N / K` be a field extension and `φ` local isomorphisms from `H` to the
split `SO_{2n}` over `K` along `Spec N ⟶ Spec K`. Suppose each Galois twist
`ψ_σ = galoisTwist φ σ` is conjugation by an invertible matrix `g_σ` over
`N`: `splitMatrix (ψ_σ(s) x) = s♯(g_σ) · splitMatrix x · s♯(g_σ⁻¹)`, with
`s♯ = sectionScalars s`.

## Matrix algebra

- `altBasis_map`: ring maps applied entrywise fix `E_ij - E_ji`.
- `commute_of_conj_map_eq`: let `κ : F → R` be an injective ring map from a
  field, and let `A' A = 1` and `B' B = 1`. If
  `κ(A) κ(U) κ(A') = κ(B) κ(U) κ(B')`, then `A' B` commutes with `U`.
  Injectivity gives `A U A' = B U B'`, and then
  `A' B U = A' (B U B') B = A' (A U A') B = U A' B`.
- `map_mul_algEquiv`, `map_one_algEquiv`: applying `σ ∈ Aut_K(F)` to
  entries is multiplicative and preserves `1`.
- `twist_mul_of_scalar`: if `g_{σσ'}⁻¹ σ(g_{σ'}) g_σ = c · 1` for a scalar
  `c`, then the twisted conjugations `θ_σ(x) = g_σ⁻¹ σ(x) g_σ` satisfy
  `θ_σ(θ_{σ'}(x)) = θ_{σσ'}(x)` for every matrix `x`. With `A = g_{σσ'}` and
  `B = σ(g_{σ'}) g_σ`, the left side is `B⁻¹ (σσ')(x) B` and `B = c A`.
  Then `c · (B⁻¹ A) = B⁻¹ B = 1`, so `B⁻¹ y B = A⁻¹ y A` for every `y`.

## The scalar cocycle

- `sectionScalars_id_injective`: the scalar map of the identity point of
  `Spec N` is the inverse of the isomorphism `Γ(Spec N) ≅ N`, so it is
  injective.
- `exists_splitMatrix_upper`, `exists_splitMatrix_lower`: on every relative
  test `V`, the unipotent orthogonal matrices `[[1, Y], [0, 1]]` and
  `[[1, 0], [Y, 1]]` with `Y = E_ij - E_ji` are matrices of points of
  `SO_{2n}`. They are the constant points of the published
  `constantPoint_upper_mem` and `constantPoint_lower_mem`, which lie in the
  identity component.
- `exists_ne_ne`: when `n ≥ 3`, any two indices of `Fin n` admit a third
  index different from both.
- `exists_scalar_cocycle` (`n ≥ 3`): `g_{σσ'}⁻¹ σ(g_{σ'}) g_σ` is a scalar
  matrix. Evaluate `ψ_{σσ'}(s) = ψ_{σ'}(s ≫ σ*) ∘ ψ_σ(s)` (`galoisTwist_mul`)
  at the identity point `s` of `Spec N` and a unipotent point `x`. The scalar
  map of `s ≫ σ*` is `s♯ ∘ σ` (`pointScalars_comp_ringTestMap`), so the two
  sides give `s♯(A) U s♯(A⁻¹) = s♯(B) U s♯(B⁻¹)`, with
  `A = g_{σσ'}` and `B = σ(g_{σ'}) g_σ`. By `commute_of_conj_map_eq`, the
  matrix `A⁻¹ B` commutes with all these unipotent matrices. By
  `eq_smul_one_of_commute` it is a scalar.

## The similitude cocycle

`exists_similitude_cocycle` assumes the published
`SpecialOrthogonalAutomorphismStatement` and `n ≥ 3`. It chooses, for each
Galois automorphism `σ`, the similitude `g_σ` of `exists_similitude_conj`
for `ψ_σ`. The resulting family has three properties:

1. each `g_σ` is a similitude: `g_σ Q g_σᵀ - ν Q` is alternating for a
   unit `ν`;
2. `θ_σ ∘ θ_{σ'} = θ_{σσ'}` on all matrices (`twist_mul_of_scalar` with
   `exists_scalar_cocycle`);
3. `ψ_σ` is conjugation by `g_σ` on all points.

These are the data from which the twisted matrix algebra with its orthogonal
involution is descended to `K`.

## Provenance

Derived. A Galois cocycle with values in `PGO_{2n}(N) = GO_{2n}(N)/Nˣ`
lifts to similitudes satisfying the cocycle identity up to scalars. The
induced twisted action on `M_{2n}(N)` gives the central simple algebra of
the form (Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*, §29.D and
§29.F). The commutation argument is elementary linear algebra and replaces
the identification of `PGO_{2n}` as the automorphism group scheme of the
matrix algebra with its quadratic pair.
