# Isotropic vectors and subspaces; hyperbolic pairs; the space `M^⊥/M`

**GKT Appendix B.2.1**: **Definition B.8**, **Proposition B.9** (existence), **Definition B.10**
(p. 612); **§4.2**: **Lemma 4.10 (a)** (p. 101), **Lemma 4.11 (a)** (pp. 101–102), **Lemma 4.14**
(the form on `M^⊥/M`, pp. 103–104); **Lemma 4.19** (first part, p. 107).

The module `Langlands.LinearAlgebra.EpsilonHermitian.Isotropic` treats totally isotropic subspaces
of an `ε`-Hermitian space over a division ring with involution (`Basic.lean`): their dual
partners, hyperbolic pairs, and the reduction `M^⊥/M`. Where a statement needs `2` invertible it
assumes `[NeZero (2 : D)]` (in a division ring, `2 ≠ 0`).

## Content

Let `h : EpsilonHermitianForm τ ε V`, `V` finite-dimensional where dimensions are used.

- `Anisotropic h` (no non-zero isotropic vector) and `IsTotallyIsotropic h U`
  (`∀ x ∈ U, ∀ y ∈ U, h x y = 0`), **Definition B.8**;
  `isTotallyIsotropic_iff_le_orthogonal : h.IsTotallyIsotropic U ↔ U ≤ h.orthogonal U`
  (**Lemma 4.10 (a)**), `IsTotallyIsotropic.mono`, `isTotallyIsotropic_bot`,
  `isTotallyIsotropic_span_singleton`.
- **Representing linear forms**: `exists_mem_forall_apply_eq` — if `Disjoint Y (h.orthogonal X)` and
  `finrank D Y = finrank D X`, then every `f : X →ₗ[D] D` is `x ↦ h x y` for some `y ∈ Y`; the
  vector is unique (`eq_of_forall_apply_eq`), and a basis `b` of `X` has a dual family `c` in `Y`,
  `h (b i) (c j) = δᵢⱼ` (`exists_dual_family`). No non-degeneracy of `h` is needed.
- **Lemma 4.11 (a)**: `exists_isTotallyIsotropic_isCompl` — for `h` non-degenerate and `X` totally
  isotropic there is a totally isotropic `X'` with `finrank D X' = finrank D X` and
  `IsCompl (h.orthogonal X) X'`; then `X ⊓ X' = ⊥` (`disjoint_of_isCompl_orthogonal`) and the form
  is non-degenerate on `X ⊕ X'` (`restrict_sup_nondegenerate`, the first part of **Lemma 4.19**).
  With `Basic.lean` (Lemma 4.18) this gives the book's `W = (X ⊕ X*) ⊕ (X ⊕ X*)^⊥` and
  `X^⊥ = X ⊕ (X ⊕ X*)^⊥`.
- **Hyperbolic pairs**: `IsHyperbolicPair h x y` (`h x x = h y y = 0`, `h x y = 1`; then
  `h y x = ε`), **Definition B.10**; `exists_apply_eq_one`; `exists_isHyperbolicPair` — a non-zero
  isotropic vector of a non-degenerate space lies in a hyperbolic pair (**Proposition B.9**,
  existence; the uniqueness of the hyperbolic plane is `StandardBasis.isometryEquiv` in
  `Lagrangian.lean`).
- **The form on a quotient**: `quotient N hN` on `V ⧸ N` for `N` in the radical, with
  `quotient_apply_mk`.
- **Lemma 4.14** (the form): `ReductionSpace h M = M^⊥ ⧸ M` (an `abbrev` for
  `h.orthogonal M ⧸ M.comap (h.orthogonal M).subtype`), `reductionMap M` the quotient map,
  `reduction M` the form `⟨w + M, w' + M⟩_M = ⟨w, w'⟩` (`reduction_apply_mk`;
  `reductionMap_eq_zero_iff`, `reductionMap_surjective`), and `reduction_nondegenerate`: it is
  non-degenerate when `h` is. The Lagrangian part of Lemma 4.14 is `IsLagrangian.reduction` in
  `Lagrangian.lean`.

**Proofs.**
- `exists_mem_forall_apply_eq`: for a basis `bᵢ` of `X`, `Y → D^m`, `y ↦ (h y bᵢ)ᵢ`, is linear
  and injective (its kernel is `Y ∩ X^⊥`), hence bijective by dimensions; choose `y` with
  `h y bᵢ = ε f(bᵢ)^τ` and use `h x y = ε h(y, x)^τ`.
- Lemma 4.11 (a) follows the book's idea without extending to a standard basis of `V`: take any
  complement `Z` of `X^⊥` (so `dim Z = dim X`), a family `zⱼ ∈ Z` dual to a basis `xᵢ` of `X`, and
  correct it to `z'ⱼ = zⱼ - ∑ₖ ½ h(zⱼ, zₖ) xₖ`, which spans a totally isotropic `X'`
  (`h(z'ᵢ, z'ⱼ) = h(zᵢ, zⱼ) + ε a_{ji}^τ + a_{ij} = 0`); `2` is invertible here.
- The non-degeneracy of `M^⊥/M` is `M^⊥⊥ = M` (`Basic.lean`), more directly than the book's
  argument through `M ⊕ M*`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
  §4.2.1, Lemmas 4.10 and 4.11, pp. 101–102; §4.2.3, Lemma 4.14, pp. 103–104; Lemma 4.19, p. 107;
  Appendix B.2, Definition B.8, Proposition B.9, Definition B.10, p. 612.

## Declarations

In `Langlands.EpsilonHermitianForm`: `Anisotropic`, `IsTotallyIsotropic`,
`isTotallyIsotropic_iff_le_orthogonal`, `IsTotallyIsotropic.mono`, `isTotallyIsotropic_bot`,
`isTotallyIsotropic_span_singleton`, `IsTotallyIsotropic.restrict_eq_zero`,
`exists_mem_forall_apply_eq`, `eq_of_forall_apply_eq`, `exists_dual_family`, `two_inv_commute'`,
`exists_isTotallyIsotropic_isCompl`, `restrict_sup_nondegenerate`,
`disjoint_of_isCompl_orthogonal`, `IsHyperbolicPair`, `IsHyperbolicPair.apply_symm`,
`exists_apply_eq_one`, `exists_isHyperbolicPair`, `quotient`, `quotient_apply_mk`,
`ReductionSpace`, `reduction`, `reductionMap`, `reduction_apply_mk`, `reductionMap_eq_zero_iff`,
`reductionMap_surjective`, `reduction_nondegenerate`.

Private: `two_inv_commute`, `conj_two_inv`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.Basic`.
- Mathlib: `LinearAlgebra.Quotient.Basic`.
