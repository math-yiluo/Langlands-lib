# Frobenius reciprocity for binary products and tensor contractions

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Frobenius`.

These are internal helper results for the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. They do not
follow a specific source; the representation-theoretic input is first adjointness
(Frobenius reciprocity) for normalized parabolic induction, which is already in the Library
(`Parabolic.FirstAdjointness.equiv`).

## Algebraic contractions (section `Algebra`)

* `rightContraction ρ τ hτ φ`: for a representation `τ` on which the group acts trivially
  and a linear functional `φ` on its space, the intertwiner `ρ ⊗ τ → ρ`,
  `a ⊗ m ↦ φ(m) a`.
* `exists_dual_rid_lTensor_ne_zero`: a nonzero tensor `w ∈ A ⊗ M` has nonzero contraction
  against some functional on `M`. Proof: expand `w` in a basis of `M`
  (`TensorProduct.equivFinsuppOfBasisRight`); some coefficient is nonzero, and the
  coordinate functional of that basis vector extracts it.
* `exists_ne_zero_of_tprod_trivial`: a nonzero intertwiner `π → ρ ⊗ τ`, `τ` trivially acted,
  gives a nonzero intertwiner `π → ρ` (compose with a suitable `rightContraction`).
* `nonempty_equiv_of_ne_zero`: a nonzero intertwiner between irreducible representations
  is an equivalence (Schur's lemma in the form `bijective_or_eq_zero`).

## Two-factor external tensors (section `External`)

* `firstSlotContraction τ φ`: for a two-factor external tensor product `τ 0 ⊠ τ 1`, the map
  `w₀ ⊗ w₁ ↦ φ(w₁) w₀`, where `φ` is a functional on the (one-factor) tail tensor; it
  intertwines the action of the first factor group, embedded by `MonoidHom.mulSingle`.
* `exists_firstFactor_ne_zero`: a nonzero intertwiner `ρ 0 ⊠ ρ 1 → τ 0 ⊠ τ 1` gives a
  nonzero intertwiner `ρ 0 → τ 0`. Proof: choose a pure tensor `⊗ v` with nonzero image;
  the map `x ↦ f(x ⊗ v 1)` intertwines `ρ 0` with the restriction of `τ 0 ⊠ τ 1` to the
  first factor group, and a suitable `firstSlotContraction` keeps `f(⊗ v)` nonzero.

## Binary products (section `Binary`)

* `intertwiningOfCompEq`: an intertwiner into `ρ ∘ φ`, where `φ g = g` for all `g`, viewed
  as an intertwiner into `ρ`.
* `exists_jacquet_ne_zero_of_isSubrepresentation` (`0 < d`, `0 < k`, `d + k = m`): if a
  nontrivial `Z` embeds into `A × σ` (the binary normalized product, rank-transported along
  `d + k = m`), then there is a nonzero intertwiner from the normalized Jacquet module of
  `Z` along the two-block shape `(d, k)` to the external tensor `A ⊠ σ`. Proof: identify
  the binary product with the normalized induction along `BlockShape.ofPair d k`
  (`SegmentSocleDerivativesProof.nonempty_ofPairProductIso`), apply first adjointness
  (`Parabolic.FirstAdjointness.equiv`), and use that the adjunction is a linear
  equivalence, so the injective (hence nonzero, as `Z` is nontrivial) embedding corresponds
  to a nonzero Jacquet-module map.
* `exists_ne_zero_of_isSubrepresentation_rankZero` (`k = 0`): if a nontrivial `Z` embeds
  into `A × σ` with `σ` on `GL_0`, there is a nonzero intertwiner `Z → A` (after the rank
  transport). Proof: `A × σ ≅ A ⊗ σ` with trivially acted `σ`
  (`binaryRightZeroTensorEquiv`), then `exists_ne_zero_of_tprod_trivial`.
