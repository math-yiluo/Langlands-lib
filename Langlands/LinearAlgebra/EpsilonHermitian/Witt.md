# Witt's theorem, the Witt decomposition and diagonalization

**GKT Appendix B.2.1**: **Theorem B.11**, **Definition B.12** (p. 612), **Theorem B.15**
(p. 613), **Theorem B.17** (p. 614). The book cites **Scharlau**, *Quadratic and Hermitian Forms*,
Chapter 7, **Theorem 9.5** (p. 269) for B.17; Scharlau's **Definition 9.3**, **Lemma 9.4** and
**Corollary 9.2** (pp. 268–269) are used too.

The module `Langlands.LinearAlgebra.EpsilonHermitian.Witt` proves Witt's extension theorem for
`ε`-Hermitian forms over a division ring with involution in which `2` is invertible
(`[NeZero (2 : D)]`), in finite dimension, for every `ε` and every involution, and derives Witt
cancellation, the equality of the dimensions of maximal totally isotropic subspaces (the Witt
index), the Witt decomposition with its uniqueness, and the diagonalization outside the
alternating case.

## Content

Let `h : EpsilonHermitianForm τ ε V` be non-degenerate, `V` finite-dimensional.

- **The alternating case**: `IsAlternatingCase τ ε : Prop := ε = -1 ∧ ∀ d, d^τ = d` (the book's
  exception "`τ` trivial and `ε = -`" in B.15). `isAlternatingCase_of_apply_self`: if all vectors of
  a subspace are isotropic but the form does not vanish on it, we are in this case (the involution
  is then inner and anti-multiplicative, hence trivial, and `D` is commutative);
  `IsAlternatingCase.apply_self`, `apply_swap`, `mul_comm`, `intCast`.
- **Reflections** (Scharlau 9.3, 9.4): for `h x x ≠ 0` and `β h(x,x) β^τ = h(x,x)`,
  `reflection hh hx hβ : h.isometryGroup`, `y ↦ y + h(y,x) h(x,x)⁻¹ (β - 1) x`
  (`reflection_apply`); it fixes `x^⊥` (`reflection_apply_of_orthogonal`).
  `exists_isometry_map_of_apply_self_eq`: if `h x x = h y y ≠ 0` there is an isometry `g` with
  `g x = y` fixing every vector orthogonal to `x` and `y`.
- **Transvections** of the alternating case: `transvection hh hA v a`, `w ↦ w + h(w,v) a v`;
  `exists_isometry_map_isHyperbolicPair`: two hyperbolic pairs are exchanged by an isometry fixing
  every vector orthogonal to the four vectors.
- **Theorem B.17** (Witt): `exists_isometry_extend_of_injective` — for a subspace `U`, an injective
  `σ : U →ₗ[D] V` with `h (σ x) (σ y) = h x y` extends to `g : h.isometryGroup`,
  `∀ x : U, g x = σ x` (`U` need not be non-degenerate).
- `finrank_inf_orthogonal_span_singleton_add_one`: `dim (U ∩ x^⊥) + 1 = dim U` for an anisotropic
  `x ∈ U`.
- **Cancellation** (Scharlau 9.2 (i)): `exists_isometry_of_isometryEquiv` (an isometry between two
  subspaces is the restriction of an isometry `g` of `V`, which maps `U^⊥` onto `U'^⊥`) and
  `nonempty_isometryEquiv_orthogonal` (isometric subspaces have isometric orthogonals).
- **Witt index** (Definition B.12): `wittIndex h`, the largest dimension of a totally isotropic
  subspace; `finrank_le_wittIndex`, `exists_isTotallyIsotropic_finrank_eq_wittIndex`, and
  `finrank_eq_wittIndex_of_maximal` (Scharlau 9.2 (ii): every maximal totally isotropic subspace has
  this dimension).
- **Theorem B.11** (Witt decomposition): `exists_wittDecomposition` — there are totally isotropic
  `X`, `X'` of dimension `wittIndex h` with `IsCompl (h.orthogonal X) X'` (so `X ⊕ X'` is a sum of
  `r = wittIndex h` hyperbolic planes), `IsCompl (X ⊔ X') (h.orthogonal (X ⊔ X'))`, and the
  anisotropic part `V_a = (X ⊕ X')^⊥` anisotropic; `wittDecomposition_unique` — in two such
  decompositions `dim X₁ = dim X₂` and the anisotropic parts are isometric.
  `exists_standardBasis_restrict_sup`: a hyperbolic space `X ⊕ X'` has a standard basis (so it is
  `ℍ ⊕ ⋯ ⊕ ℍ`). A split space in the sense of Definition B.12 (`V_a = 0`) is split in the sense of
  Definition 4.7 (`Lagrangian.lean`).
- **Theorem B.15** (diagonalization): `exists_orthogonal_basis` — outside the alternating case a
  non-degenerate space has an orthogonal basis `b` of anisotropic vectors,
  `V = ⟨a₁⟩ ⊕ ⋯ ⊕ ⟨aₙ⟩` with `aᵢ = h(bᵢ, bᵢ)`; `exists_orthogonal_family` for non-degenerate
  subspaces; `linearIndependent_of_orthogonal`.

## Proof of Witt's theorem

Strong induction on Scharlau's measure `dim U + 2 dim (U ∩ U^⊥)` (`wittMeasure`), in three cases.

1. `U` contains an anisotropic `x`: `U = D x ⊕ U₁` with `U₁ = U ∩ x^⊥`, which has the same radical
   and one dimension less. By induction `σ|_{U₁}` extends to `g₁`; `y = g₁⁻¹ σ x` has
   `h(y,y) = h(x,x)` and is orthogonal to `U₁`, and an isometry `g₂` fixing `{x, y}^⊥ ⊇ U₁` sends
   `x` to `y`; `g = g₁ g₂`. The isometry `g₂` is Scharlau's: if `z = x - y` is anisotropic, the
   reflection `r_{z,β}` with `β = 1 - h(z,z) h(x,z)⁻¹`; the identity `β h(z,z) β^τ = h(z,z)`
   (which Scharlau leaves to the reader) follows from `h(x,z) + h(z,x) = h(z,z)`; if `x - y` is
   isotropic then `x + y` is not (`h(x+y,x+y) + h(x-y,x-y) = 4 h(x,x)`), and
   `r_{y,-1} r_{x+y,β}` works.
2. All vectors of `U` are isotropic but the form does not vanish on `U`: this is the alternating
   case (`isAlternatingCase_of_apply_self`). Split off a hyperbolic pair `x, y` of `U` (two
   dimensions, same radical) and use symplectic transvections instead of reflections; this is the
   case Scharlau's Theorem 9.5 excludes.
3. `U` is totally isotropic and non-zero: with dual partners `U'` of `U` and `S'` of `σ U`
   (Lemma 4.11 (a)), `σ` extends to `U ⊕ U'` by sending `u' ∈ U'` to the `s' ∈ S'` with
   `h(σ u, s') = h(u, u')` (Scharlau's `σ ⊕ (σ*)⁻¹`); `U ⊕ U'` is non-degenerate, so its measure
   `2 dim U` is smaller than `3 dim U`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
  Appendix B.2, Theorem B.11 and Definition B.12, p. 612; Theorem B.15, p. 613; Theorem B.17,
  p. 614.
- W. Scharlau, *Quadratic and Hermitian Forms* (Springer, 1985), Chapter 7, §9: Corollary 9.2,
  Definition 9.3 and Lemma 9.4, p. 268; Theorem 9.5, pp. 269–270.

## Declarations

In `Langlands.EpsilonHermitianForm`: `IsAlternatingCase`, `IsAlternatingCase.mul_comm`,
`IsAlternatingCase.intCast`, `IsAlternatingCase.apply_swap`, `IsAlternatingCase.apply_self`,
`isAlternatingCase_of_apply_self`, `reflectionMap`, `reflectionMap_apply`,
`reflectionMap_map_apply`, `reflection`, `reflection_apply`, `reflection_apply_of_orthogonal`,
`neg_one_mul_apply_self_mul_neg_one`, `exists_isometry_map_of_apply_self_eq`, `transvectionMap`,
`transvectionMap_apply`, `transvectionMap_map_apply`, `transvection`, `transvection_apply`,
`exists_isometry_map_isHyperbolicPair`, `finrank_inf_orthogonal_span_singleton_add_one`,
`exists_isometry_extend_of_injective`, `exists_isometry_of_isometryEquiv`,
`nonempty_isometryEquiv_orthogonal`, `wittIndex`, `finrank_le_wittIndex`,
`exists_isTotallyIsotropic_finrank_eq_wittIndex`, `finrank_eq_wittIndex_of_maximal`,
`exists_wittDecomposition`, `exists_standardBasis_restrict_sup`, `wittDecomposition_unique`,
`linearIndependent_of_orthogonal`, `exists_orthogonal_family`, `exists_orthogonal_basis`.

Private: `apply_add_smul`, `reflection_scalar`, `exists_isometry_map_of_sub`,
`exists_transvection_map`, `exists_transvection_map'`, `wittMeasure`, `witt_step_anisotropic`,
`witt_step_alternating`, `bddAbove_wittIndex`, `exists_le_finrank_eq`, `maximal_of_anisotropic`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.Lagrangian`.
- Mathlib: `Tactic.NoncommRing`.
