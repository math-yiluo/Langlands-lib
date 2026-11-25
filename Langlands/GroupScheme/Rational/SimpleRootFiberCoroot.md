# The coroot of a simple relative root fiber as a morphism from a Weil restriction

Module `Langlands.GroupScheme.Rational.SimpleRootFiberCoroot`, namespaces
`Langlands.GroupScheme.SplitPinning`, `Langlands.GroupScheme` and
`Langlands.GroupScheme.SimpleRootFiber`.

Part of the SL2 half of the algebraic rank-one coordinates of
`AlgebraicRankOneCoordinatesExistenceStatement`, assembled in
`Geometry.Building.AlgebraicSL2RootCoordinatesConstruction`.

## Purpose

`AlgebraicSL2RootCoordinates` asks for a morphism
`coroot : (WeilGm.commGroupScheme k E).toGrp ⟶ Z.toGrp` from the Weil restriction of `𝔾ₘ`
along the coordinate field `E`. Its rational points must be the diagonal matrices:
`j (coroot u) = rho (diag u)` for `u ∈ Eˣ`. The field `E` need not be Galois over `k`.

This module builds that morphism for the data of `SimpleRootFiberPinning`: the pinning
`fiberPinning`, the fiber `O = fiberSet a` of a simple relative root `a`, the fiber field
`E = fiberField` and the embeddings `τ = fiberEmbedding`. For `rho` it uses the descended
homomorphism `SplitPinning.fieldSL2` of `OrthogonalOrbitSpecialLinear`.

## General lemmas

- `SplitPinning.rationalCharacterEval_simpleCorootPoint`: a character `χ` takes the value
  `t ^ ⟨χ, α_b^∨⟩` at the simple-coroot point `α_b^∨(t)`. This is the private lemma
  `eval_cocharacter` of the Library module `SimpleCorootCoordinates`, restated for simple
  coroots.
- `IsSplitTorus.rationalPoint_ext`: rational points of a split torus with the same
  character values are equal (from `IsSplitTorus.point_ext_characters`).

## Members and embeddings (section `Members`)

Assume `K/k` is Galois and `j` is closed, as in the `Field` section of
`SimpleRootFiberPinning`.

- `memberOf σ` is the member of the fiber whose root corresponds to the embedding
  `σ : E →ₐ[k] K` under `rootRestrictionFiberEmbeddingEquiv` (`exists_member`,
  `memberOf_mem`, `rootOf_memberOf`).
- `fiberEmbedding_memberOf`, `memberOf_fiberEmbedding` and `memberEquiv : O ≃ (E →ₐ[k] K)`:
  the members of the fiber correspond bijectively to the embeddings of `E`.
- `memberOf_comp`: `memberOf (σ ∘ φ) = action σ (memberOf φ)`, by `fiberEmbedding_galois`.

## The coroot morphism (section `Coroot`)

- `fiberField_embeddingEvaluation_bijective`: `E ⊗_k K ≅ K^{Hom(E, K)}`, by the Library's
  `embeddingEvaluationStatement` and `WeilGm.intermediate_minpoly_splits`.
- `corootCharacterMap : X^*(T_K) →+ X^*((R_{E/k} 𝔾ₘ)_K)` sends `χ` to the character with
  embedding coordinates `σ ↦ ⟨χ, α^∨_{memberOf σ}⟩`, using `WeilGm.embeddingCharacterEquiv`.
- `coroot_action`: Galois transport of the simple coroots of the pinning, from
  `GaloisCompatiblePinningData.action_coroot` (the torus identification is the identity).
- `corootCharacterMap_equivariant`: `corootCharacterMap` is Galois equivariant. The Galois
  action on characters of the Weil restriction is the permutation representation on
  embeddings (`WeilGm.galoisRepresentation_embeddingCharacterEquiv_symm`). The check
  combines `memberOf_comp`, `coroot_action` and `latticePairing_galoisRepresentation_right`.
- `existsUnique_coroot`, `fiberCoroot`, `fiberCoroot_comp`: by
  `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`, there is exactly one
  morphism `fiberCoroot : R_{E/k} 𝔾ₘ ⟶ T` over `k` whose base change pulls characters back
  by `corootCharacterMap`.

## Rational points (section `Points`)

Assume `[Fintype O]`.

- `orbitCoroot_eq_map_prod`: `orbitCoroot` (module `Rational.OrthogonalOrbitCorootWords`) over `O` is the image under the
  pinning inclusion of `∏_{b ∈ O} α_b^∨(u_b)`. This is the first step of the Library proof
  of `orbitCoroot_eq_map_simpleCorootProduct`, without the hypothesis `u = 1` off `O`.
- `map_baseChange_map_fiber`: `j_K` is the pinning inclusion, as in
  `OrthogonalOrbitRootCoordinates.map_baseChange_map`.
- `fiberCoroot_extendedUnitPoint`: after scalar extension, `fiberCoroot` sends `u ∈ Eˣ` to
  `∏_{b ∈ O} α_b^∨(τ_b u)` in `T(K)`. Proof by `IsSplitTorus.rationalPoint_ext`. A character
  `χ` gives `∏_σ σ(u)^{⟨χ, α^∨_{memberOf σ}⟩}` on the left
  (`WeilGm.rationalCharacterEval_extendedUnitPoint_eq_prod`) and
  `∏_{b ∈ O} (τ_b u)^{⟨χ, α_b^∨⟩}` on the right. The two products agree after reindexing by
  `memberEquiv`.
- `fiberCoroot_points`: if `2 • a` is not a relative root, then
  `j (fiberCoroot u) = fieldSL2 (diag u)` on rational points. Both sides are compared after
  scalar extension to `K` (injective for affine groups). The right side is
  `orbitCoroot (τ · u)` (`rationalExtend_fieldSL2_diag`).

## Provenance

Internal. The construction is the standard Weil restriction of the coroots of a Galois orbit
of orthogonal simple roots, `R_{E/k} 𝔾ₘ → T`, `u ↦ ∏_σ α_σ^∨(σ u)`. It is carried out with
the Library's Galois descent of homomorphisms into split tori
(`FiniteGaloisCharacterDescent`) and its embedding coordinates on Weil restrictions
(`WeilRestrictionEmbeddingLattices`, `WeilRestrictionRationalCharacters`). No source
theorem is cited. Every step is proved in Lean.
