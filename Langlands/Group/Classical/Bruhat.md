# The Bruhat decomposition and the generalized Bruhat decomposition

**GKT §4.4.2** (pp. 116–117): the Bruhat decomposition with respect to the Siegel parabolic and the
`c`-part; **§4.4.3**: **Proposition 4.30** (p. 118) and **Theorem 4.31** (pp. 119–121); overview in
§4.1.5 (pp. 99–100).

The module `Langlands.Group.Classical.Bruhat` proves, for a non-degenerate `-ε`-Hermitian form over a
division ring with involution in which `2` is invertible, the Bruhat decomposition
`G = ⋃_S P w_S P` with its characterization by `dim (X ∩ g X)` and by the `c`-part, and the
generalized Bruhat decomposition of pairs `(g₁, g₂)` with the Leray invariant
`L(X, g₁⁻¹ X, g₂ X)`.

## Setting

`h : EpsilonHermitianForm τ (-ε) V` (the book's `W`), `e : h.StandardBasis ι` with `ι` finite,
`X = e.lagrangianFst = span {eᵢ}`, `Y = e.lagrangianSnd = span {eᵢ*}`, `P = siegelParabolic h X`,
`w_S = e.weylElement S`, `n(b) = siegelUnipotentOf … b hb` (`SiegelParabolic.lean`). A partition
`S₀ ⊔ ⋯ ⊔ S₄` of the index set is a map `σ : ι → Fin 5` (`Sⱼ = σ⁻¹ j`). `[NeZero (2 : D)]` is
assumed where five-term decompositions are used (they need partners of totally isotropic
subspaces, Lemma 4.11 (a)).

## Content

- **Coordinate subspaces** (GKT (4.7)): for `A : Set ι`, `blockFst A = X_A = span {eᵢ | i ∈ A}`,
  `blockSnd A = Y_A`, `block A = W_A = X_A ⊕ Y_A`; `finrank_blockFst`, `finrank_blockSnd`,
  `finrank_block` (for `A : Finset ι`: `|A|`, `|A|`, `2 |A|`), `block_le_orthogonal` (blocks of
  disjoint index sets are orthogonal), `block_sup_block_compl`, `disjoint_block_compl`,
  `restrict_block_nondegenerate`, `isLagrangian_blockFst`, `isLagrangian_blockSnd` (`X_A`, `Y_A`
  are Lagrangians of `W_A`), `blockFst_sup_blockFst_compl`, `blockSnd_sup_blockSnd_compl`,
  `isOrthogonalDecomposition_block` (the blocks of the fibres of `σ : ι → κ` form an orthogonal
  decomposition, GKT p. 120), and small lemmas listed below.
- **Orbits of pairs** (§4.4.2): `exists_isometry_map_pair_iff` — there is `g ∈ G` with `g X₁ = Y₁`,
  `g X₂ = Y₂` iff `dim (X₁ ∩ X₂) = dim (Y₁ ∩ Y₂)`; proved from Corollary 4.25 with `X₃ = X₂`
  (`lerayM_self : M(X₁, X₂, X₂) = X₂`, so the Leray invariants live on zero spaces,
  `isometryEquivOfSubsingleton`).
- **Bruhat decomposition**: `map_weylElement_lagrangianFst : w_S X = X_{Sᶜ} ⊕ Y_S`,
  `lagrangianFst_inf_map_weylElement : X ∩ w_S X = X_{Sᶜ}`,
  `finrank_lagrangianFst_inf_map_weylElement : dim (X ∩ w_S X) + |S| = n`;
  `mem_doubleCoset_weylElement_iff : g ∈ P w_S P ↔ dim (X ∩ g X) + |S| = n`;
  `exists_mem_doubleCoset : G = ⋃_S P w_S P`;
  `mem_doubleCoset_weylElement_iff_card : w_{S'} ∈ P w_S P ↔ |S| = |S'|`.
- **The `c`-part**: `siegelCPart hXY g : X →ₗ[D] Y`, the `Y`-component of `g|_X` for a polarization
  `V = X ⊕ Y` (any sign); `mem_ker_siegelCPart` (`x ∈ ker c(g) ↔ g x ∈ X`),
  `finrank_ker_siegelCPart : dim ker c(g) = dim (X ∩ g X)`, and
  `mem_doubleCoset_weylElement_iff_finrank_ker : g ∈ P w_S P ↔ |S| = n - dim ker c(g)` (the book's
  `|S| = n - dim_D ker(c)`).
- **The form of `b`**: `siegelHermForm hb U hU : EpsilonHermitianForm τ ε U`,
  `(y, y') ↦ h (b y) y'` for `b ∈ Herm(Y, X)` and `U ≤ Y` (`siegelHermForm_apply`), the book's
  `(Y_{S₄}, (-, -)_b)`; `exists_siegelHerm_add_mem` — for Lagrangians `X, Y, Z` with `Z` a complement
  of `X` there is `b ∈ Herm(Y, X)` with `y + b y ∈ Z` (i.e. `n(b) Y = Z`); `b y = q y - y` with `q`
  the projection onto `Z` along `X`.
- **Proposition 4.30 in coordinates**: `exists_mem_siegelParabolic_map_eq` — for Lagrangians
  `X₂, X₃` there are `σ`, `b ∈ Herm(Y, X)` vanishing on `Y_{S₄ᶜ}` with values in `X_{S₄}`, and
  `p ∈ P` with `p κ₁⁻¹ X = X₂`, `p κ₂ X = X₃`, `κ₁ = w_{S₁ ∪ S₂ ∪ S₄}`,
  `κ₂ = n(b) w_{S₁ ∪ S₃ ∪ S₄}`, and `L(X, X₂, X₃) ≅ (Y_{S₄}, (-, -)_b)`.
- **Theorem 4.31**: `exists_generalizedBruhat` — for `g₁, g₂ ∈ G` there are `σ`, `b` as above and
  `p₁, p, p₂ ∈ P` with `g₁ = p₁ κ₁ p⁻¹`, `g₂ = p κ₂ p₂⁻¹`; the form `(Y_{S₄}, (-, -)_b)` is
  non-degenerate and isometric to `L(X, g₁⁻¹ X, g₂ X)`.
  `nonempty_isometryEquiv_lerayInvariant_of_eq_mul`: whenever `g₁ = p₁ κ₁ p⁻¹`, `g₂ = p κ₂ p₂⁻¹`
  with `p₁, p, p₂ ∈ P(X)`, `L(X, g₁⁻¹ X, g₂ X) ≅ L(X, κ₁⁻¹ X, κ₂ X)` (the book's last display), using
  (4.3) and `nonempty_isometryEquiv_lerayInvariant_of_eq` (equal triples).

## Proof of Theorem 4.31

As in the book: take a five-term decomposition `V = W₀ ⊕ ⋯ ⊕ W₄` of `(X, X₂, X₃)`
(`nonempty_fiveTermDecomposition`), choose `σ` with `|Sⱼ| = dim (X ∩ Wⱼ) = ½ dim Wⱼ` (private
`exists_fiber_card`; `Σⱼ dim Wⱼ = dim V` from the internal direct sum), and isometries
`hⱼ : W_{Sⱼ} ≅ Wⱼ` with `hⱼ X_{Sⱼ} = Wⱼ ∩ X` and, for `j = 1, 2, 3, 4`, `hⱼ Y_{Sⱼ} = Wⱼ ∩ X₂`,
`Wⱼ ∩ X₂`, `Wⱼ ∩ X₃`, `Wⱼ ∩ X₂` (`exists_isometryEquiv_map_isLagrangian`,
`exists_isometryEquiv_map_polarization`), glued to `Φ = h₀ ⊕ ⋯ ⊕ h₄ ∈ P`
(`exists_isometryEquiv_of_decomposition`; private `exists_isometryEquiv_fiveTerm`). Then
`b` is defined from the Lagrangian `Ẑ = Y_{S₄ᶜ} ⊕ Φ⁻¹(X₃ ∩ W₄)`, a complement of `X`, by
`exists_siegelHerm_add_mem` (private `exists_siegelHerm_fiveTerm`). One checks `Φ κ₁⁻¹ eᵢ ∈ X₂` and
`Φ κ₂ eᵢ ∈ X₃` for every `i` by cases on `σ i`, using the conditions (0)–(3) of the five-term
decomposition, whence `Φ κ₁⁻¹ X = X₂` and `Φ κ₂ X = X₃` (`map_lagrangianFst_eq`,
`IsLagrangian.eq_of_le`). Finally `p₁ = g₁ Φ κ₁⁻¹`, `p = Φ`, `p₂ = g₂⁻¹ Φ κ₂`. The Leray invariant:
`L(X, X₂, X₃) ≅` Leray form of `(X ∩ W₄, X₂ ∩ W₄, X₃ ∩ W₄)` (Corollary 4.23), and `Φ` carries
`(Y_{S₄}, (-, -)_b)` onto it (private `nonempty_isometryEquiv_siegelHermForm`; the projection onto
`X₃ ∩ W₄` along `X ∩ W₄` sends `Φ y` to `Φ (y + b y)`).

## Remarks on the book's text

- The book proves Theorem 4.31 from Proposition 4.30, whose `ρ₁ = diag(1, τ₁, τ₂, 1, τ₄)` and
  `ρ₂` involve maps `τᵢ = [[0, I], [-ε I, 0]]` that depend on unstated identifications
  `I : Wᵢ ∩ Xⱼ → Wᵢ ∩ Xᵢ`, and the identity `hᵢ⁻¹ τᵢ hᵢ = w_{Sᵢ}` needs `hᵢ` compatible with them.
  Here Proposition 4.30 is replaced by its coordinate form `exists_mem_siegelParabolic_map_eq`: the
  element `Φ ∈ P` is shown directly to carry `(X, κ₁⁻¹ X, κ₂ X)` to `(X, X₂, X₃)`, which is all the
  proof of Theorem 4.31 uses; the `τᵢ`, `ρᵢ` are not formalized.
- The book's last assertion `L(X, κ₁⁻¹ X, κ₂ X) = L(X_{S₄}, w_{S₄} X_{S₄}, n(b) w_{S₄} X_{S₄})` (a
  Leray invariant of `W_{S₄}`) is not stated; what is proved is that both `L(X, g₁⁻¹ X, g₂ X)` and
  `L(X, κ₁⁻¹ X, κ₂ X)` are isometric to `(Y_{S₄}, (-, -)_b)`, which is the content used later.
- The book's representatives `w_i = w_{\{1, …, i\}}` are one choice of `S` with `|S| = i`; the
  statements here are for arbitrary `S`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §4.1.5,
  pp. 99–100; Lemma 4.9, p. 101; §4.4.2, pp. 116–117; §4.4.3, (4.11) and Proposition 4.30,
  pp. 117–119; Theorem 4.31 and its proof, pp. 119–121.

## Declarations

In `Langlands.EpsilonHermitianForm`: `mem_orthogonal_span_iff`, `isometryEquivOfSubsingleton`,
`lerayM_self`, `exists_isometry_map_pair_iff`, `siegelCPart`, `mem_ker_siegelCPart`,
`finrank_ker_siegelCPart`, `IsometryEquiv.nondegenerate`, `IsLagrangian.eq_of_le`,
`siegelHermForm`, `siegelHermForm_apply`, `exists_siegelHerm_add_mem`,
`nonempty_isometryEquiv_lerayInvariant_of_eq`, `nonempty_isometryEquiv_lerayInvariant_of_eq_mul`.

In `Langlands.EpsilonHermitianForm.StandardBasis`: `blockFst`, `blockSnd`, `block`,
`fst_mem_blockFst`, `snd_mem_blockSnd`, `fst_mem_block`, `snd_mem_block`, `blockFst_univ`,
`blockSnd_univ`, `blockFst_le_lagrangianFst`, `blockSnd_le_lagrangianSnd`, `finrank_blockFst`,
`finrank_blockSnd`, `apply_basis_eq_zero_of_ne`, `block_eq_span`, `block_le_orthogonal`,
`block_sup_block_compl`, `blockFst_le_block`, `blockSnd_le_block`, `restrict_block_nondegenerate`,
`disjoint_blockFst_blockSnd`, `disjoint_blockFst_blockSnd_comap`, `isOrthogonalDecomposition_block`,
`finrank_block`, `isLagrangian_blockFst`, `isLagrangian_blockSnd`, `map_weylElement_lagrangianFst`,
`lagrangianFst_inf_map_weylElement`, `finrank_lagrangianFst_inf_map_weylElement`,
`mem_doubleCoset_weylElement_iff`, `mem_doubleCoset_weylElement_iff_finrank_ker`,
`exists_mem_doubleCoset`, `mem_doubleCoset_weylElement_iff_card`, `blockFst_sup_blockFst_compl`,
`blockSnd_sup_blockSnd_compl`, `disjoint_block_compl`, `map_lagrangianFst_eq`,
`weylElement_inv_fst_of_mem`, `weylElement_inv_fst_of_not_mem`,
`exists_mem_siegelParabolic_map_eq`, `exists_generalizedBruhat`.

Private: `subsingleton_reductionSubmodule`, `fin_five_cases`, `exists_fiber_card`,
`disjoint_comap_subtype`, `map_eq_inf_of_map_comap`, `exists_isometryEquiv_fiveTerm`,
`exists_siegelHerm_fiveTerm`, `nonempty_isometryEquiv_siegelHermForm`.

## Dependencies

- `Langlands.Group.Classical.SiegelParabolic`.
