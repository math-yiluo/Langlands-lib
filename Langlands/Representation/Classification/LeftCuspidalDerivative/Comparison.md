# The comparison step: from `𝔄 × Y` to `𝔄 × E`

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Comparison`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. Its main
result is the image argument behind the comparison clause (clause 3). It follows the
classical argument of Jantzen 2007 (Lemma 2.1.2) and Mínguez 2009 (§3). Only the
mathematics stated in the Lean declarations below is claimed.

## Tensor contractions (generic)

Here `ι` is an index type with decidable equality, `H i` are groups, and `J`, `ρ`, `τ` are
families of representations of the `H i`. `FiniteTensor.external` is the external tensor
product, a representation of `∀ i, H i`. `MonoidHom.mulSingle H k` is the inclusion of the
coordinate group `H k`.

* `exists_slot_ne_zero`: a nonzero intertwiner from a representation `π` of `H k` into the
  restriction of `FiniteTensor.external J` to `H k` yields a nonzero intertwiner
  `π → J k`. Proof:
  * `FiniteTensor.slotEquiv` identifies the restriction with `(⊗_{i ≠ k} J i) ⊗ J k`, on
    which `H k` acts trivially on the first factor (`FiniteTensor.action_slotRestriction_compl`).
  * A suitable functional on the first factor does not kill the image of some vector
    (`exists_dual_lid_rTensor_ne_zero`, module `Criterion`).
  * Contract with it (`FiniteTensor.trivialContraction`).
* `exists_slot_map_ne_zero` (finite `ι`): a nonzero intertwiner
  `external ρ → external τ` yields a nonzero intertwiner `ρ k → τ k` for every `k`. Proof:
  choose a pure tensor `⊗ v_i` with nonzero image. The map `x ↦ ⊗ (v with v_k replaced by x)`
  is `H k`-equivariant. Compose and apply `exists_slot_ne_zero`.
* `isSubquotient_slot_of_injective` (finite `ι`): suppose a representation `Z` on a nontrivial
  space embeds into `external J` and `J k` is irreducible. Then `J k` is a quotient, hence
  a subquotient, of the restriction of `Z` to `H k`. The nonzero map comes from
  `exists_slot_ne_zero`; it is surjective because `J k` is irreducible.
* `isSubquotient_of_injective`: the source of an injective intertwiner is a subquotient of
  its target. Use the range and `JuxtaposedShuffle.rangeEquivOfInjective`.

## Binary products

Throughout, `B = (a, m)` is the two-block shape `BlockShape.ofPair a m`, with `a, m > 0`.

* `exists_equiv_twoBlock_of_isSubquotient`: let `𝔄` be irreducible and `Z` an irreducible
  smooth subquotient of `𝔄 ⊠ Y` on the Levi subgroup of `B`. Then there is an irreducible
  subquotient `E` of `Y` with `Z ≃ 𝔄 ⊠ E`. Proof:
  * `Z` is admissible (`CuspidalSupport.irreducibleLeviAdmissibility`), so it factors as
    `X 0 ⊠ X 1` with irreducible factors (`CuspidalSupport.padicLeviAdmissibleFactorization`).
  * Restricting to each block, `X k` is a subquotient of the factor `k` of `𝔄 ⊠ Y`
    (`isSubquotient_external_comp_mulSingle`, `isSubquotient_factor_of_external_comp_mulSingle`,
    module `PieceTools`).
  * So `X 0 ≃ 𝔄` (`CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient`), and
    `E = X 1` is a subquotient of `Y`.
* `isSubrepresentation_of_jacquet_ne_zero` (Frobenius reciprocity, converse direction): a
  nonzero intertwiner from the normalized Jacquet module of an irreducible `π` along `B` to
  `𝔄 ⊠ E` gives an embedding of `π` into `𝔄 × E`. Proof:
  * Use `Parabolic.FirstAdjointness.equiv` and
    `SegmentSocleDerivativesProof.nonempty_ofPairProductIso`.
  * The resulting intertwiner is nonzero, hence injective because `π` is irreducible.
* `isSubquotient_jacquetInduction_of_isSubrepresentation`: if `P` embeds into the normalized
  product `×_C X`, the Jacquet module of `P` along `C` is a subquotient of the Jacquet module
  of `×_C X` along `C`. This holds because the normalized Jacquet functor preserves
  injections (`JuxtaposedShuffle.normalizedJacquetMap_injective`).
* `isSubrepresentation_of_twoBlock_equiv`: if `Z ≃ 𝔄 ⊠ E` embeds into `𝔄 ⊠ Y` (`𝔄`, `E`
  irreducible), then `E` embeds into `Y`. Apply `exists_slot_map_ne_zero` at the second
  coordinate; the resulting nonzero map is injective because `E` is irreducible.

## The comparison step

`exists_isSubrepresentation_of_isSubrepresentation_binaryProduct`: let `A` be supercuspidal on
`GL_d`, `𝔄` irreducible and `A`-pure on `GL_a`, and `Y` left `A`-reduced on `GL_m`
(`d, a, m > 0`). If an irreducible `π` embeds into `𝔄 × Y`, then there is an irreducible
subrepresentation `E` of `Y` such that `π` embeds into `𝔄 × E`. Proof:

1. Frobenius reciprocity (`exists_jacquet_ne_zero_of_isSubrepresentation`, module
   `Frobenius`) gives a nonzero `g : r_B(π) → 𝔄 ⊠ Y`. The Jacquet module `r_B(π)` has finite
   length (`Parabolic.normalizedParabolicFiniteLength`).
2. The image of `g` has an irreducible quotient `Z'` that is a quotient of `r_B(π)`
   (`SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero`). By
   `exists_equiv_twoBlock_of_isSubquotient`, `Z' ≃ 𝔄 ⊠ E` for an irreducible subquotient `E`
   of `Y`. The composite `r_B(π) → Z' ≃ 𝔄 ⊠ E` is nonzero, so `π` embeds into `𝔄 × E`
   (`isSubrepresentation_of_jacquet_ne_zero`). Moreover `E` is left `A`-reduced, by clause 1
   (`leftReduced_of_isSubquotient`, module `Basic`).
3. The image of `g` also has an irreducible subrepresentation `Z`. It is a subquotient of
   `r_B(π)` and embeds into `𝔄 ⊠ Y` (`exists_irreducible_of_hom_ne_zero`, module
   `FirstBlock`). Hence `𝔄` is a subquotient of the restriction of `Z` to `GL_a`
   (`isSubquotient_slot_of_injective`). Also, `Z` is a subquotient of the Jacquet module of
   `𝔄 × E` (`isSubquotient_jacquetInduction_of_isSubrepresentation`).
4. By the `𝔄`-type constituent theorem `nonempty_equiv_of_isSubquotient_jacquetInduction`
   (module `Core`), `Z ≃ 𝔄 ⊠ E`. So `𝔄 ⊠ E` embeds into `𝔄 ⊠ Y`, and
   `isSubrepresentation_of_twoBlock_equiv` gives `E ↪ Y`.

No finite-length hypothesis on `Y` is needed.
