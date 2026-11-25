# Rao's five-term decomposition

**GKT §4.3**: **Lemma 4.19** (p. 107), **Lemma 4.21** (pp. 108–109), **Proposition 4.22** with its
dimension formulas (pp. 110–111), **Corollary 4.23**, **Lemma 4.24** (p. 111), **Corollary 4.25**
(p. 112).

The module `Langlands.LinearAlgebra.EpsilonHermitian.FiveTerm` proves Rao's five-term
decomposition of a triple of Lagrangians of a non-degenerate `ε`-Hermitian space over a division
ring with involution in which `2` is invertible, computes the Leray invariant on its last piece, and
classifies triples up to the isometry group (the orbits of `G(W)` on `Ω × Ω × Ω`).

## Content

Let `h` be non-degenerate on a finite-dimensional `V`; `[NeZero (2 : D)]` where partners of
totally isotropic subspaces are used (Lemma 4.11 (a)).

- Preliminaries: `exists_le_inf_eq_bot_sup_eq` (a complement inside a subspace),
  `restrict_sup_nondegenerate_of_orthogonal` (an orthogonal sum of non-degenerate subspaces is
  non-degenerate), `orthogonal_eq_inf_sup` (`N^⊥ = (N^⊥ ∩ A) ⊕ A^⊥` for `N ≤ A`, `A`
  non-degenerate), `inf_orthogonal_eq_bot_of_isCompl`, `orthogonal_inf_sup_eq_left`,
  `orthogonal_inf_sup_eq_right` (for `V = M^⊥ ⊕ M*`, both `M` and `M*` are Lagrangians of
  `M ⊕ M*`), `isLagrangian_comap_of_le_orthogonal` (Lemma 4.20 for two pieces).
- **Lemma 4.19**: `isSplit_restrict_sup` — for totally isotropic `M₁, M₂` with `V = M₁^⊥ ⊕ M₂`,
  `M₁ ∩ M₂ = 0` and `M₁ ⊕ M₂` is non-degenerate and split.
- Lagrangians of a subspace: `isLagrangian_restrict_iff` (`X ≤ U` is a Lagrangian of `(U, h|_U)` iff
  `X^⊥ ∩ U = X`) and `orthogonal_inf_inf_eq` (Lemma 4.20 inside a subspace).
- **Lemma 4.21**: `IsSplitting h U A B X₁ X₂ X₃` — `U = A ⊕ B` orthogonally with `A, B`
  non-degenerate, the `Xᵢ` commute with `(A, B)`, `X₁ = X₂` on `A`, `X₁` and `X₂` transverse on `B`
  (with `disjoint`, `le_left`, `le_right`, and the transport `IsSplitting.map_subtype`);
  `exists_isSplitting` (for `U = V`) and `exists_isSplitting_of_le` (inside a non-degenerate
  subspace `U`, for three Lagrangians of `U`). The proof is the book's: first for
  `X₁ ∩ X₂ ∩ X₃ = 0` with `A = M ⊕ M*`, `M = X₁ ∩ X₂`, `M* ⊆ X₃` a complement of `M^⊥` (private
  `exists_isSplitting_of_inf_eq_bot`), then in general with `V₁ = M₀ ⊕ M₀*`,
  `M₀ = X₁ ∩ X₂ ∩ X₃`, and the first case applied in `V₂ = V₁^⊥`, transported back along
  `V₂ → V`.
- **Proposition 4.22**: `FiveTermDecomposition h X₁ X₂ X₃`, a structure with the pieces
  `W : Fin 5 → Submodule D V`, the orthogonal decomposition, the commuting of the three Lagrangians,
  and the conditions (0)–(4) of the book (`eq₀₁₂`, `eq₀₁₃`, `disjoint₁`, `eq₁`, `disjoint₂`, `eq₂`,
  `disjoint₃`, `eq₃`, `disjoint₄₁₂`, `disjoint₄₂₃`, `disjoint₄₁₃`); `nonempty_fiveTermDecomposition`
  (existence, by Lemma 4.21 applied four times as in the book: `V = V₁ ⊕ V₂`, `V₁ = W₀ ⊕ W₃`,
  `V₂ = W₂ ⊕ V₃`, `V₃ = W₁ ⊕ W₄`). The pieces carry Lagrangians (`isLagrangian_comap₁/₂/₃`), and
  - `inf_inf_eq : X₁ ∩ X₂ ∩ X₃ = X₁ ∩ W₀`, `inf₂₃_eq : X₂ ∩ X₃ = (X₁ ∩ W₀) ⊕ (X₂ ∩ W₁)`,
    `inf₁₃_eq : X₁ ∩ X₃ = (X₁ ∩ W₀) ⊕ (X₁ ∩ W₂)`, `inf₁₂_eq : X₁ ∩ X₂ = (X₁ ∩ W₀) ⊕ (X₁ ∩ W₃)`;
  - the dimension formulas `finrank_W₀ : dim W₀ = 2 dim (X₁ ∩ X₂ ∩ X₃)`,
    `finrank_W₁ : dim W₁ + dim W₀ = 2 dim (X₂ ∩ X₃)`, `finrank_W₂`, `finrank_W₃`
    (`finrank_W_eq`, `finrank_comap_subtype`, `IsOrthogonalDecomposition.disjoint`);
  - `lerayM_eq : M(X₁, X₂, X₃) = (X₁ ∩ W₀) + (X₂ ∩ W₁) + (X₁ ∩ W₂) + (X₁ ∩ W₃)`.
- **Corollary 4.23** (for `h` `-ε`-Hermitian): `isTransverseTriple₄` (the `Xᵢ ∩ W₄` are a transverse
  triple of `W₄`), `W₄_le_orthogonal_lerayM`, the isometry `isometryEquivReduction : W₄ ≅ M^⊥/M`,
  `w ↦ w + M` (onto because every vector of `M^⊥` is congruent modulo `M` to its component in
  `W₄`), `map_isometryEquivReduction` (it carries `Xᵢ ∩ W₄` to `X_{iM}`), and
  `nonempty_isometryEquiv_lerayInvariant`: `L(X₁, X₂, X₃) = L(X₁ ∩ W₄, X₂ ∩ W₄, X₃ ∩ W₄)`.
- **Lemma 4.24, Corollary 4.25**: `exists_isometry_map_iff` — there is `g` in the isometry group
  with `g Xᵢ = Yᵢ` (`i = 1, 2, 3`) iff `dim (X₁ ∩ X₂ ∩ X₃) = dim (Y₁ ∩ Y₂ ∩ Y₃)`,
  `dim (Xᵢ ∩ Xⱼ) = dim (Yᵢ ∩ Yⱼ)` and `L(X₁, X₂, X₃) ≅ L(Y₁, Y₂, Y₃)`. The proof builds, as the
  book does, isometries `W_j ≅ W'_j` of the pieces of two five-term decompositions
  (`exists_isometryEquiv_map_isLagrangian` for `W₀`, `exists_isometryEquiv_map_polarization` for
  `W₁, W₂, W₃`, Lemma 4.17 with Corollary 4.23 for `W₄`) and glues them
  (`exists_isometryEquiv_of_decomposition`). The book's condition (iv) is not stated separately.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §4.3.1,
  Lemmas 4.18–4.21, pp. 107–109; §4.3.2, Proposition 4.22, pp. 110–111; Corollary 4.23, p. 111;
  §4.3.3, Lemma 4.24, p. 111; Corollary 4.25, p. 112.

## Declarations

In `Langlands.EpsilonHermitianForm`: `exists_le_inf_eq_bot_sup_eq`,
`restrict_sup_nondegenerate_of_orthogonal`, `orthogonal_eq_inf_sup`,
`inf_orthogonal_eq_bot_of_isCompl`, `orthogonal_inf_sup_eq_left`, `orthogonal_inf_sup_eq_right`,
`isLagrangian_comap_of_le_orthogonal`, `isSplit_restrict_sup`, `isLagrangian_restrict_iff`,
`orthogonal_inf_inf_eq`, `IsSplitting` (fields `sup_eq`, `le_orthogonal`, `nondegenerate_left`,
`nondegenerate_right`, `commutes₁`, `commutes₂`, `commutes₃`, `inf_left`, `disjoint_right`),
`IsSplitting.disjoint`, `IsSplitting.le_left`, `IsSplitting.le_right`, `IsSplitting.map_subtype`,
`exists_isSplitting`, `exists_isSplitting_of_le`, `FiveTermDecomposition` (fields as above),
`nonempty_fiveTermDecomposition`, `finrank_comap_subtype`, `IsOrthogonalDecomposition.disjoint`,
`FiveTermDecomposition.isLagrangian_comap₁`, `isLagrangian_comap₂`, `isLagrangian_comap₃`,
`finrank_W_eq`, `inf_inf_eq`, `inf₂₃_eq`, `inf₁₃_eq`, `inf₁₂_eq`, `finrank_W₀`, `finrank_W₁`,
`finrank_W₂`, `finrank_W₃`, `lerayM_eq`, `isTransverseTriple₄`, `W₄_le_orthogonal_lerayM`,
`isometryEquivReduction`, `map_isometryEquivReduction`, `nonempty_isometryEquiv_lerayInvariant`;
`exists_isometryEquiv_map_isLagrangian`, `exists_isometryEquiv_map_polarization`,
`exists_isometry_map_iff`.

Private: `exists_isSplitting_of_inf_eq_bot`, `inf_inf_of_le`, `component_eq_zero`, `component_mem`,
`sum_five`, `finrank_sup_of_pieces`, `component_mem_lagrangian`, `sub_component_mem_lerayM`,
`comap_eq_of_inf_eq`, `disjoint_comap`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.Decomposition`.
