# The Leray invariant of a triple of Lagrangians

**GKT §4.2.2–§4.2.4**: **Lemma 4.12**, **Definition 4.13** (p. 103), **Definition 4.15** with
(4.2) (p. 105), **Lemma 4.16** (pp. 105–106), **Lemma 4.17** (pp. 106–107); **(4.3)** (p. 112);
**§4.3.4**: **Proposition 4.26** (p. 113).

The module `Langlands.LinearAlgebra.EpsilonHermitian.LerayInvariant` defines the Leray invariant of
a triple of Lagrangians of a non-degenerate `-ε`-Hermitian space over a division ring with
involution (any field of characteristic `≠ 2` in the book; nothing here uses `2`), and proves its
symmetry, its invariance under isometries and similitudes, and the classification of transverse
triples.

## Setting and conventions

`h : EpsilonHermitianForm τ (-ε) V` is non-degenerate on a finite-dimensional left `D`-module `V`
(the book's right space `W`, see `Basic.lean`); the Leray invariant is an `ε`-Hermitian form, as in
the book. The book's invariant is an isometry class; here it is a representative form, and
"`L = L'`" is stated as `Nonempty (IsometryEquiv L L')`. For the symplectic case (`D = F`,
`τ = id`, `ε = 1`, `h` alternating, e.g. `ofBilinForm B`) the Leray invariant is a symmetric
bilinear form, the quadratic space of GKT §4.5.2 used in Theorem 5.2.

## Content

- `IsTransverseTriple h X₁ X₂ X₃`: three Lagrangians, pairwise transverse (§4.2.2), with
  `swap₁₂`, `swap₂₃`, `swap₁₃`, `isCompl₃₁`, `isCompl₁₂`.
- `lerayProj hT hh : V →ₗ[D] V`, the projection onto `X₃` along `X₁` (`lerayProj_mem`,
  `lerayProj_sub_mem`, `lerayProj_eq_of`). For `x ∈ X₂` it is the book's `u x = x + b x`, where `u` is
  the unique isometry that is the identity on `X₁` and maps `X₂` to `X₃` (Lemma 4.9); no choice of
  `u` is needed.
- **Lemma 4.12, Definition 4.13**: `lerayForm h hT hh : EpsilonHermitianForm τ ε X₂`,
  `(x, x')_b = h (p x) x'` (`lerayForm_apply`); it equals the book's `⟨b x, x'⟩`
  (`lerayForm_apply_eq_sub`) and `⟨u x, x'⟩` for any such isometry `u`
  (`lerayForm_apply_of_isometry`); it is non-degenerate (`lerayForm_nondegenerate`). The key identity
  is `lerayProj_apply_add`: `h(p x, y) + h(x, p y) = 0` for `x, y ∈ X₂`, read off `h(p x, p y) = 0`.
- **Naturality**: `lerayFormIsometryEquiv` — an isometry `φ : V ≅ V'` carrying one transverse
  triple to another is an isometry of the Leray forms (through `φ|_{X₂}`);
  `isometryEquivOfIsometryGroup` turns an element of the isometry group into an isometry.
- **Lemma 4.16**: `nonempty_isometryEquiv_lerayForm_swap₁₂`, `…_swap₂₃`, `…_swap₁₃` —
  `L(X₂, X₁, X₃) = L(X₁, X₃, X₂) = L(X₃, X₂, X₁) = -L(X₁, X₂, X₃)`, through `b : X₂ → X₁`,
  `p : X₂ → X₃` and the identity respectively (the book's maps); even permutations follow by
  composition.
- **Lemma 4.17** (for two spaces): `exists_isometryEquiv_iff_lerayForm` — two transverse triples (of
  two non-degenerate spaces) are carried to each other by an isometry iff their Leray forms are
  isometric. The converse direction is the book's: extend the isometry of Leray forms
  `σ : X₂ ≅ X₂'` to `φ` with `φ X₁ = X₁'` (Lemma 4.9 across two spaces,
  `exists_isometryEquiv_extend` of `Lagrangian.lean`) and check `φ X₃ ⊆ X₃'^⊥`.
- **Isometries of `M^⊥/M`**: `reductionEquiv φ hM` (an isometry with `φ M = M'` induces
  `M^⊥/M ≅ M'^⊥/M'`), `reductionEquiv_apply_mk`, `map_reductionSubmodule` (it carries `X_M` to
  `(φ X)_{M'}`), and `reductionEquivOfEqBot` with `map_reductionSubmodule_eqBot` (`M = 0`).
- **Definition 4.15**: `lerayM X₁ X₂ X₃ = X₁ ∩ X₂ + X₂ ∩ X₃ + X₃ ∩ X₁` (`lerayM_comm₁₂`,
  `lerayM_comm₂₃`, `lerayM_rotate`, `lerayM_eq_bot`), totally isotropic
  (`isTotallyIsotropic_lerayM`); `sup_lerayM_inf_sup_lerayM : (X₁ + M) ∩ (X₂ + M) = M`, whence the
  images `X_{iM}` in `M^⊥/M` form a transverse triple (`isTransverseTriple_reduction`), and
  `lerayInvariant h hh h₁ h₂ h₃ : EpsilonHermitianForm τ ε (h.reductionSubmodule (lerayM X₁ X₂ X₃) X₂)`
  is their Leray form (`lerayInvariant_nondegenerate`). For a transverse triple it is the Leray form
  of Definition 4.13 (`nonempty_isometryEquiv_lerayInvariant_lerayForm`).
- **(4.3)**: `nonempty_isometryEquiv_lerayInvariant_map` (an isometry `V ≅ V'`) and
  `nonempty_isometryEquiv_lerayInvariant_map_isometryGroup` (`L(gX₁, gX₂, gX₃) = L(X₁, X₂, X₃)`),
  with `map_lerayM` and `IsLagrangian.map_isometryEquiv`.
- **Proposition 4.26**: `nonempty_isometryEquiv_lerayInvariant_similitude` — for a linear
  isomorphism `T : V ≅ V'` with `h'(T x, T y) = a h(x, y)` (`a` non-zero, central, `a^τ = a`),
  `L(T X₁, T X₂, T X₃) = a L(X₁, X₂, X₃)`. Tools: `orthogonal_smul`, `isLagrangian_smul_iff`,
  `nondegenerate_smul`, `lerayForm_smul` (scaling the form scales the Leray form),
  `reductionSmulEquiv`, `map_reductionSmulEquiv`.

## Remarks on the book's text

- Before Definition 4.15 the book justifies the transversality of the `X_{iM}` by `Xᵢ ∩ Xⱼ ⊆ M`;
  what is needed is `(Xᵢ + M) ∩ (Xⱼ + M) = M`, which holds (`sup_lerayM_inf_sup_lerayM`, a
  computation in the lattice of subspaces).
- The book derives (4.3) and Proposition 4.26 from the five-term decomposition (Corollaries 4.23,
  4.25). Here both are proved directly, by naturality of the construction; Proposition 4.26 uses
  that `M^⊥/M` for `a h` is `M^⊥/M` for `h` with the form multiplied by `a`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
  §4.2.2–4.2.4, Lemma 4.12, Definition 4.13, p. 103; Lemma 4.14, Definition 4.15, pp. 103–105;
  Lemmas 4.16 and 4.17, pp. 105–107; (4.3), p. 112; Proposition 4.26, pp. 112–113.

## Declarations

In `Langlands.EpsilonHermitianForm`: `IsTransverseTriple` (fields `isLagrangian₁`, `isLagrangian₂`,
`isLagrangian₃`, `disjoint₁₂`, `disjoint₂₃`, `disjoint₁₃`), `IsTransverseTriple.swap₁₂`, `swap₂₃`,
`swap₁₃`, `isCompl₃₁`, `isCompl₁₂`, `lerayProj`, `lerayProj_mem`, `lerayProj_sub_mem`,
`lerayProj_eq_of`, `lerayProj_apply_add`, `lerayForm`, `lerayForm_apply`, `lerayForm_apply_eq_sub`,
`lerayForm_apply_of_isometry`, `lerayForm_nondegenerate`, `lerayFormIsometryEquiv`,
`isometryEquivOfIsometryGroup`, `finrank_eq_of_isLagrangian`,
`nonempty_isometryEquiv_lerayForm_swap₁₂`, `nonempty_isometryEquiv_lerayForm_swap₂₃`,
`nonempty_isometryEquiv_lerayForm_swap₁₃`, `exists_isometryEquiv_iff_lerayForm`, `reductionEquiv`,
`reductionEquiv_apply_mk`, `map_reductionSubmodule`, `reductionEquivOfEqBot`,
`map_reductionSubmodule_eqBot`, `lerayM`, `lerayM_comm₁₂`, `lerayM_comm₂₃`, `lerayM_rotate`,
`lerayM_eq_bot`, `sup_lerayM_inf_sup_lerayM`, `isTotallyIsotropic_lerayM`,
`isTransverseTriple_reduction`, `lerayInvariant`, `lerayInvariant_nondegenerate`,
`nonempty_isometryEquiv_lerayInvariant_lerayForm`, `IsLagrangian.map_isometryEquiv`, `map_lerayM`,
`nonempty_isometryEquiv_lerayInvariant_map`,
`nonempty_isometryEquiv_lerayInvariant_map_isometryGroup`, `orthogonal_smul`,
`isLagrangian_smul_iff`, `nondegenerate_smul`, `lerayForm_smul`, `reductionSmulEquiv`,
`map_reductionSmulEquiv`, `nonempty_isometryEquiv_lerayInvariant_similitude`.

Private: `equivOfInjective`, `le_orthogonal_of_le_lagrangian`, `mem_sup_of_reductionMap_mem`,
`disjoint_reductionSubmodule`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.Witt` (and through it `Lagrangian`, `Isotropic`,
  `Basic`).
