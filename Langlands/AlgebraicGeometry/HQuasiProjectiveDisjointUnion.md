# Disjoint unions of H-quasi-projective schemes

Helper module of the proof of
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement` (entry
module `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof`).
It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry`. `A` is a commutative ring. `IsHQuasiProjective` and
`IsHProjective` are the Library predicates: a quasi-compact immersion, respectively a closed
immersion, into some `ProjectiveSpace A n`, commuting with the maps to `Spec A`.

- Instance `compactSpace_projectiveSpace`: `ProjectiveSpace A n` is quasi-compact.
- `IsHQuasiProjective.compactSpace`: an H-quasi-projective scheme is quasi-compact.
- `isHQuasiProjective_of_isEmpty`: an empty scheme is H-quasi-projective.
- `isEmpty_pullback_of_disjoint`, `mem_iff_of_disjoint`: elementary facts on disjoint opens.
- `isHQuasiProjective_of_disjoint_cover`: let `X ⟶ Spec A` be covered by finitely many pairwise
  disjoint opens `V θ`, each H-quasi-projective over `Spec A`, with immersions
  `i θ : V θ ⟶ ℙ^{n θ}_A`. Then `X` is H-quasi-projective.
  *Proof.* Put `N + 1 = 1 + Σ_θ (n θ + 1)` and choose an injection
  `e θ : Fin (n θ + 1) → Fin (N + 1)` for each `θ`. Their images are pairwise disjoint, and one
  index lies outside all of them. Compose `i θ` with the coordinate embedding
  `ℙ^{n θ}_A ⟶ ℙ^N_A` along `e θ` (module `ProjectiveSpace.CoordinateEmbedding`). Glue these
  morphisms to `g : X ⟶ ℙ^N_A`; the overlaps are empty. Let `W θ` be the union of the coordinate
  opens `D₊(X (e θ k))`, and let `W none` be the coordinate open of the remaining index. These
  opens cover `ℙ^N_A`, and `g⁻¹(W θ) = V θ`, `g⁻¹(W none) = ∅`. On `W θ` the morphism `g` is
  `i θ` followed by a closed immersion, hence an immersion. Being an immersion is local on the
  target. Finally `g` is quasi-compact because `g ≫ (ℙ^N_A ⟶ Spec A) = p` is quasi-compact
  (`X` is a finite union of quasi-compact opens) and `ℙ^N_A` is separated over `Spec A`.
- `isHQuasiProjective_of_isImmersion_of_isHProjective`: if `X` is quasi-compact,
  `k : X ⟶ Y` is an immersion and `q : Y ⟶ Spec A` is H-projective, then `k ≫ q` is
  H-quasi-projective. Compose `k` with the closed immersion of `Y`. The composite is
  quasi-compact because `X` is quasi-compact and `ℙⁿ_A` is separated over the affine `Spec A`.
- `isHQuasiProjective_of_disjoint_cover_of_compactSpace`: the version of
  `isHQuasiProjective_of_disjoint_cover` for a quasi-compact `X` and an arbitrary index type.
  A finite subcover suffices, since the remaining opens are empty.
- `isClosed_of_disjoint_cover`: each member of a cover by pairwise disjoint opens is closed.
  Its complement is the union of the others.
- `isHQuasiProjective_of_isImmersion_of_disjoint_cover`: let `X` be quasi-compact and
  `j : X ⟶ H` an immersion. Let `πH : H ⟶ Spec A`, and let `H` be covered by pairwise disjoint
  opens `U θ` with each `(U θ).ι ≫ πH` H-projective. Then `j ≫ πH` is H-quasi-projective.
  The preimages `j⁻¹(U θ)` are pairwise disjoint and cover `X`. Each is closed in `X`, hence
  quasi-compact. On `j⁻¹(U θ)` the composite is the immersion `j ∣_ U θ` followed by the
  H-projective `U θ ⟶ Spec A`.

## Use

The quotient `Q` in the entry module is quasi-compact and immerses into the Hilbert scheme
`H`. `HilbertSchemeUniversalFamilyStatement` covers `H` by pairwise disjoint H-projective opens
`U θ`, indexed by Hilbert polynomials `θ`. So `Q` is H-quasi-projective by
`isHQuasiProjective_of_isImmersion_of_disjoint_cover`. This is step 5 of the intended proof in
`FlatProperEquivalenceRelationQuotientReductionStatement.md`.
