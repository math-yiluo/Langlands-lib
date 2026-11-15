# Generic tools for the analysis of geometric pieces

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.PieceTools`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It collects
three general facts used in the analysis of the pieces of the geometric lemma for a binary
product. None of them is specific to `GL_n`; they are standard facts about exact functors,
restriction of representations and external tensor products, proved here directly from the
Library API. No hypothesis beyond those displayed in the Lean statements is used.

## Extraction

* `subsingleton_map_of_preservesFiniteLengthShortExact`: a functor `Φ` between categories of
  smooth complex representations that preserves short exact sequences of finite-length
  representations (`SmoothRep.PreservesFiniteLengthShortExact Φ`) sends a finite-length
  representation with subsingleton carrier to a representation with subsingleton carrier.
  Proof: the sequence `Z → Z → Z` made of identity maps is short exact when `Z` is zero, so
  its image `Φ Z → Φ Z → Φ Z` is exact at the middle term; exactness of `𝟙, 𝟙` there forces
  every vector to be zero.
* `exists_irreducible_of_isSubquotient_map_of_finiteLength`: if `Φ` is as above, `Z` has
  finite length, and an irreducible `X` is a subquotient of `Φ Z`, then there is an
  irreducible subquotient `τ` of `Z` such that `X` is a subquotient of `Φ τ`.
  Proof: take a composition series of `Z` (`isFiniteLength_iff_exists_compositionSeries`) and
  argue by induction along it. The bottom term is zero, so its image is zero and cannot
  contain the nontrivial `X`. At a step `S_i ⋖ S_{i+1}`, the short exact sequence
  `S_i → S_{i+1} → S_{i+1}/S_i` is sent by `Φ` to an exact sequence, and an irreducible
  subquotient of the middle term is a subquotient of one of the outer terms
  (`SegmentHeadSupport.smooth_isSubquotient_or_of_exact`); the quotient `S_{i+1}/S_i` is
  irreducible because the step is a covering
  (`LengthCriterionProof.isIrreducible_quotientRep_iff`). The top term is `Z` itself, up to the
  isomorphism `⊤ ≅ Z`. This is the finite-length analogue of the Library lemma
  `SegmentHeadSupport.exists_irreducible_of_isSubquotient_map`, which requires full
  exactness.

## Restriction

* `restrictionFunctor φ hφ`: for a continuous group homomorphism `φ : H →* G`, the functor
  from smooth representations of `G` to smooth representations of `H` sending `A` to
  `A.representation.comp φ` (smooth by `Langlands.isSmooth_comp`) and keeping the underlying
  linear maps. `restrictionFunctor_obj_representation` records the object formula (by `rfl`).
* `restrictionFunctor_preservesFiniteLengthShortExact`: this functor preserves short exact
  sequences of finite-length representations, since the underlying linear maps are
  unchanged.

## Slot

Here `J i` is a family of representations of groups `H i` indexed by a finite type `ι`, and
`FiniteTensor.external J` is their external tensor product, a representation of `∀ i, H i`.
Restriction to the coordinate `k` means composition with `MonoidHom.mulSingle H k`.

* `isSubquotient_factor_of_external_comp_mulSingle`: an irreducible subquotient `ρ` of the
  restriction of `FiniteTensor.external J` to coordinate `k` is a subquotient of `J k`.
  Proof: the restriction is `J k` tensored with a trivial representation of `H k`
  (`FiniteTensor.slotEquiv`, `FiniteTensor.action_slotRestriction_compl`), and irreducible
  subquotients of such a tensor product are subquotients of the first factor
  (`FiniteTensor.isSubquotient_of_tprod_trivial`).
* `isSubquotient_external_comp_mulSingle`: if all carriers are nontrivial, then `J k` is a
  subquotient of the restriction of `FiniteTensor.external J` to coordinate `k`. Proof: in
  the same splitting, contract the trivial factor against a functional that takes the value
  `1` on a nonzero vector (`FiniteTensor.trivialContraction`); the contraction is a surjective
  intertwiner onto `J k`.
