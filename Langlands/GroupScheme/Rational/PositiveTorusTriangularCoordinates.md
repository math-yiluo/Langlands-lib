# Torus-weighted triangular coordinates on the standard unipotent subgroup

## Statement

The module defines one proposition and proves nothing.

`PositiveTorusTriangularCoordinatesStatement` quantifies over:

- a field `F` of characteristic zero (`[CharZero F]`) in universe `u`;
- an affine group scheme `G` over `Spec F`, locally of finite type, with
  `IsConnectedReductive G`;
- a commutative group scheme `T` with a homomorphism `i : T ⟶ G` such that
  `IsMaximalSplitTorus i`;
- a cocharacter `ν` of `T` with `IsGenericCocharacter i ν` (no relative root pairs to zero
  with `ν`).

Let `N := Standard.unipotentScheme i ν ∅` with inclusion `ι := Standard.unipotentHom i ν ∅`.
This is the Library's closed representative of the standard unipotent subgroup for the
empty set of simple roots. The proposition asserts that there exist `d : ℕ`, global functions
`t : Fin d → AffineCoordinateRing F N.X`, polynomials
`P : Fin d → MvPolynomial (Fin d ⊕ Fin d) F` and characters `w : Fin d → characterLattice T`
such that:

1. **Polynomial coordinates.** `MvPolynomial.aeval t : F[X₀, …, X_{d-1}] → 𝒪(N)` is
   bijective.
2. **Triangularity.** Every variable of `P k` is `Sum.inl j` or `Sum.inr j` with `j < k`.
3. **Group law.** For every `F`-algebra `A : CommAlgCat F`, all `x, y ∈ N(A)` and every `k`,
   `t_k(x * y) = t_k(x) + t_k(y) + P_k(t(x), t(y))`, where `Sum.inl j ↦ t_j(x)` and
   `Sum.inr j ↦ t_j(y)`.
4. **Torus weights.** For every `F`-algebra `A`, every `s ∈ T(A)` and all `x, y ∈ N(A)` with
   `ι(y) = i(s) · ι(x) · i(s)⁻¹` in `G(A)`, and every `k`,
   `t_k(y) = w_k(s) · t_k(x)`. Here `w_k(s) ∈ Aˣ` is `Lie.characterValue (w k) s`. Points of
   `T` and `N` are mapped to `G(A)` by `GroupScheme.affinePointsTarget`.
5. **Weights are positive roots.** Every `w k` lies in `positiveRelativeRoots i ν`, the
   relative roots `β` with `0 < ⟨β, ν⟩`.
6. **Multiplicities.** For every `β ∈ positiveRelativeRoots i ν`, the number of indices `k`
   with `w k = β` is `Module.finrank F (weightSpace i β)`. Here `weightSpace i β` is the
   Library's `β`-weight space of `T` in `Lie(G)(F)`: the `X` with
   `Ad(i(s)) X_A = β(s) X_A` for every `F`-algebra `A` and every `s ∈ T(A)`.

Conditions 1–3 are literally the three conditions of the Library's
`HasTriangularCoordinates N` (`Langlands/GroupScheme/TriangularCoordinates.lean`). The
quantifier over `A` ranges over `CommAlgCat.{u} F` there as well.

## Relation to `UnipotentTriangularCoordinatesStatement`

The Library's `UnipotentTriangularCoordinatesStatement` says that every smooth connected
unipotent affine group of finite type over a field of characteristic zero satisfies
`HasTriangularCoordinates`. It applies to all such groups. It gives no information about a
torus action, and its coordinates come from an arbitrary filtration of the Lie algebra by
ideals.

The present proposition applies only to the standard unipotent subgroup `N` of a connected
reductive group with respect to a maximal split torus. It also requires the coordinates to
be weight vectors for conjugation by `T`, with the weights and multiplicities in conditions
4–6. Neither proposition implies the other as Lean statements: the present one does not
cover arbitrary unipotent groups, and the Library one gives no torus weights. Mathematically
both rest on the exponential map of a unipotent group in characteristic zero. The ordering of
the coordinates differs: here it is by `ν`-height, not by a filtration by ideals.

## Source and provenance

The proposition is derived; it is not stated in this form in the literature. It is the
algebraic input for a computation of the Haar modulus of conjugation by the positive torus
on the adelic points of `N`. That modulus is the Library proposition
`PositiveTorusUnipotentModulusStatement`
(`Langlands/Global/AdelicSiegelMeasureReduction.lean`). Its hypotheses (number field, connected
reductive `G`, maximal split torus, generic `ν`) are copied here so that the proposition
applies directly in that use.

Sources:

- J. S. Milne, *Algebraic Groups* (Cambridge, 2017), registered source
  `milne-2017-algebraic-groups`, SHA256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:
  Theorem 3.23 (Cartier; printed p. 71, PDF p. 87); 14.31 (the exponential
  `exp : Lie(U)_a → U` of a unipotent group in characteristic zero and the identity
  `g · exp(X) · g⁻¹ = exp(Ad(g) X)`; printed p. 288, PDF p. 304); Proposition 14.32
  (`exp` is an isomorphism of schemes; printed p. 289, PDF p. 305); 14.35 (the
  Campbell–Hausdorff series `H = Σ H_m`, `H_1 = U + V`, `H_m` for `m ≥ 2` a rational
  combination of iterated brackets of length `m`; printed pp. 290–291); Proposition 14.36
  (`exp(x) exp(y) = exp(H(x, y))` for all `k`-algebras `R` and `x, y ∈ 𝔤_R`; printed p. 291,
  PDF p. 307).
- B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive groups*, 2nd ed. (Cambridge, 2015),
  registered source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`: Proposition 2.1.8
  (printed p. 53, PDF p. 79): for `λ : GL₁ → G`, `Lie(U_G(λ)) = 𝔤₊`, the sum of the
  positive weight spaces of `GL₁` acting through `λ`; `U_G(λ)` is smooth with connected
  fibres when `G` is smooth. The statement of Proposition 2.1.10 (printed p. 58, PDF p. 84)
  calls `U_G(λ)` a smooth connected unipotent group.

### Derivation

Write `Φ⁺ := positiveRelativeRoots i ν` and `ht(χ) := ⟨χ, ν⟩ ∈ ℤ`.

**Step 1: `N = U_G(ν)`, with `Lie(N) = ⊕_{β ∈ Φ⁺} 𝔤_β`.** Since `T` is split, `Lie(G)` is
the direct sum of the weight spaces `𝔤_χ`. By CGP 2.1.8(1), `Lie(U_G(ζ))` is the sum of the
`𝔤_χ` with `⟨χ, ζ⟩ > 0`. For `ζ = ν` this is `⊕_{β ∈ Φ⁺} 𝔤_β`: a character with nonzero
weight space and positive height is nonzero, hence a relative root.
`N` is the intersection of `U_G(ζ)` over the standard cocharacters `ζ` for `∅`, those
positive on every simple relative root. `ν` is one of them, since simple roots are positive.
Every `β ∈ Φ⁺` is a sum of simple roots: if `β` is not simple, then `β = β₁ + β₂` with
`βᵢ ∈ Φ⁺`, and `ht(βᵢ) < ht(β)` because heights of positive roots are positive integers.
Hence every standard `ζ` is positive on `Φ⁺`, and `Lie(U_G(ν)) ⊆ Lie(U_G(ζ))`. The
intersection `U_G(ν) ∩ U_G(ζ)` is smooth by Cartier's theorem (characteristic zero). Its Lie
algebra is `Lie(U_G(ν)) ∩ Lie(U_G(ζ)) = Lie(U_G(ν))`, so it has the dimension of the smooth
connected group `U_G(ν)` and contains it. So `N = U_G(ν)`, a smooth connected unipotent
group normalized by `i(T)`, with `Lie(N) = ⊕_{β ∈ Φ⁺} 𝔤_β`.

**Step 2: coordinates.** Choose a basis `e_0, …, e_{d-1}` of `Lie(N)` with each `e_k` in
some `𝔤_{w_k}`, `w_k ∈ Φ⁺`, ordered so that `ht(w_0) ≤ ht(w_1) ≤ ⋯`. Exactly
`dim 𝔤_β` basis vectors lie in `𝔤_β`, which gives conditions 5 and 6. Let `t_k` be the
`k`-th coordinate of `exp⁻¹ : N → Lie(N)_a`. Milne 14.32 gives condition 1.

**Step 3: group law.** By Milne 14.36, `log(xy) = H(log x, log y)`, and `H_1 = X + Y` gives
the linear part. Since `Ad(i(s))` is a Lie algebra automorphism,
`[𝔤_α, 𝔤_β] ⊆ 𝔤_{α+β}`. An iterated bracket of length `m ≥ 2` of basis vectors
`e_{j_1}, …, e_{j_m}` therefore lies in `𝔤_{w_{j_1} + ⋯ + w_{j_m}}`. Its `e_k`-coordinate
vanishes unless `w_k = w_{j_1} + ⋯ + w_{j_m}`. In that case
`ht(w_k) = Σ ht(w_{j_l}) > ht(w_{j_l})` for each `l`, because all heights are positive and
`m ≥ 2`. By the height ordering, every `j_l < k`. Brackets of length greater than the maximal
height vanish, so `H(X, Y) - X - Y` is a finite sum. Expanding it multilinearly in the
coordinates gives `P_k` with coefficients in `F`, involving only indices `< k`. This is
conditions 2 and 3, for every `F`-algebra `A`.

**Step 4: torus weights.** Embed `G` in some `GL_V`. By Milne 14.31, applied to the
restriction of `V` to `N`, `exp` on `Lie(N)_A` is the matrix exponential of nilpotent
matrices. So for `s ∈ T(A)`, `i(s) · exp(X) · i(s)⁻¹ = exp(Ad(i(s)) X)`. If
`ι(y) = i(s) ι(x) i(s)⁻¹`, then `log y = Ad(i(s)) (log x)`. On `𝔤_β ⊗ A` the operator
`Ad(i(s))` is multiplication by `β(s)`; this is the defining property of `weightSpace i β`.
Taking `e_k`-coordinates gives `t_k(y) = w_k(s) · t_k(x)`, which is condition 4.

The derivation uses neither `IsConnectedReductive G` nor `IsGenericCocharacter i ν`, and it
uses only the split-torus part of `IsMaximalSplitTorus i`. These hypotheses are included
because the downstream use assumes them.
