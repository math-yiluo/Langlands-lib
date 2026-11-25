# Orthogonal decompositions of an `ε`-Hermitian space

**GKT §4.3.1**: orthogonal decompositions, "commuting with the decomposition", **Lemma 4.20**
(p. 108).

The module `Langlands.LinearAlgebra.EpsilonHermitian.Decomposition` provides the tools of GKT §4.3
for an orthogonal decomposition `V = W₁ ⊕ ⋯ ⊕ W_k` of an `ε`-Hermitian space over a division ring
with involution into non-degenerate subspaces: components, subspaces commuting with the
decomposition, Lemma 4.20, gluing of isometries, and the transport of notions along the inclusion of
a subspace. Nothing here needs `2` to be invertible or a non-degenerate ambient form (it follows).

## Content

Let `h : EpsilonHermitianForm τ ε' V` and `W : ι → Submodule D V`.

- `CommutesWith W X : Prop := ⨆ i, X ⊓ W i = X` (the book: `X = (W₁ ∩ X) ⊕ ⋯ ⊕ (W_k ∩ X)`).
- `IsOrthogonalDecomposition h W`: `W i ≤ (W j)^⊥` for `i ≠ j`, `⨆ i, W i = ⊤`, and every `W i`
  non-degenerate (`apply_eq_zero`). Then the `W i` are independent (`iSupIndep`), `V` is their
  internal direct sum (`isInternal`), and, for a finite index type, `component i : V →ₗ[D] V` is the
  component in `W i` (`component_mem`, `component_of_mem`, `sum_component : ∑ i, component i v = v`,
  `component_apply_self`); the form is computed piece by piece (`apply_eq_sum_component`), and `h`
  is non-degenerate (`nondegenerate_form`).
- For `X` commuting with the decomposition: components of vectors of `X` lie in `X`
  (`component_mem_of_commutesWith`, `component_mem_inf`, `mem_iff_component_mem`); intersections of
  commuting subspaces commute (`commutesWith_inf`).
- **Lemma 4.20**: `IsOrthogonalDecomposition.isLagrangian_comap` — a Lagrangian `X` commuting with
  the decomposition meets each piece in a Lagrangian of that piece:
  `(h.restrict (W i)).IsLagrangian (X.comap (W i).subtype)`; in particular each piece is split and
  `dim W i = 2 dim (W i ∩ X)`. The proof is direct (a vector of `W i` orthogonal to `X ∩ W i` is
  orthogonal to all of `X`), not the book's dimension count.
- **Gluing**: `exists_isometryEquiv_of_decomposition` — isometries `φ i : W i ≅ W' i` between the
  pieces of two orthogonal decompositions (of two spaces) glue to an isometry `Φ : V ≅ V'` with
  `Φ w = φ i w` on `W i` (the book's `g = g₀ ⊕ ⋯ ⊕ g₄` in Lemma 4.24).
- **Transport along `U → V`**: `restrict_orthogonal_comap`
  (`(h|_U)^⊥ (A ∩ U) = (h^⊥ (A ∩ U)) ∩ U` as subspaces of `U`),
  `restrict_restrict_nondegenerate_iff`, `isTotallyIsotropic_map_subtype_iff`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §4.3.1,
  Lemma 4.20, p. 108.

## Declarations

`Langlands.CommutesWith`; in `Langlands.EpsilonHermitianForm`: `restrict_orthogonal_comap`,
`restrict_restrict_nondegenerate_iff`, `isTotallyIsotropic_map_subtype_iff`,
`IsOrthogonalDecomposition` (fields `orthogonal`, `iSup_eq_top`, `nondegenerate`), and in its name
space `apply_eq_zero`, `iSupIndep`, `isInternal`, `component`, `component_mem`, `component_of_mem`,
`sum_component`, `component_apply_self`, `apply_eq_sum_component`, `nondegenerate_form`,
`component_mem_of_commutesWith`, `mem_iff_component_mem`, `commutesWith_inf`, `component_mem_inf`,
`isLagrangian_comap`; `exists_isometryEquiv_of_decomposition`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.LerayInvariant`.
- Mathlib: `Algebra.DirectSum.Module`.
