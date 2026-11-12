# Arithmetic transport preserves the standard archimedean compact subgroup

This module is an internal construction. It combines the published arithmetic
transport of infinite adeles (`AdelicFunctoriality.infiniteAdeleEquiv`,
`AdelicGLTransport.infiniteEquiv`) with the standard compact subgroup
`standardInfiniteCompact` of `ArchimedeanCompact`. The two Mathlib inputs are
the uniqueness of ring endomorphisms of `ℝ` and
`Complex.ringHom_eq_id_or_conj_of_continuous`: a continuous ring endomorphism
of `ℂ` is the identity or complex conjugation. No new object from the original
literature is identified here. The published special case for the CM
involution is `complexConj_comap_standardInfiniteCompact` in
`AmbientArithmeticTransport`. This module proves the same fact for every field
isomorphism.

Throughout, `K : Type uK`, `L : Type uL` and `M : Type uM` are number fields in
independent universes, `e : K ≃+* L` is a ring isomorphism and `n` is any natural
rank, including zero. `infinitePlaceEquiv e` sends an infinite place `w` of `L`
to the place `x ↦ w (e x)` of `K`.

## Places and coordinates

- `isReal_infinitePlaceEquiv_iff` and `isComplex_infinitePlaceEquiv_iff`:
  `infinitePlaceEquiv e w` is real (complex) exactly when `w` is. The first is
  Mathlib's `isReal_comap_iff`.
- `realPlace e` and `complexPlace e` restrict `infinitePlaceEquiv e` to the real
  and complex places of `L`, with values in the real and complex places of `K`.
- `extensionEmbeddingOfIsReal_infiniteCompletionMap`: at a real place `w` of
  `L`, the completed map `infiniteCompletionMap e w` becomes the identity of
  `ℝ` in the real embeddings of the two completions. The proof reads the
  composite as a ring endomorphism of `ℝ`, which must be the identity.
- `extensionEmbedding_infiniteCompletionMap`: at a complex place `w` of `L`,
  the completed map, read in the complex embeddings of the two completions,
  is either the identity of `ℂ` at every point or complex conjugation at every
  point. The composite is a continuous ring endomorphism of `ℂ`, so the Mathlib
  theorem above applies. Which case occurs depends on the place.
- `mixedSpace_infiniteAdeleEquiv_fst` and `mixedSpace_infiniteAdeleEquiv_snd`
  state the same facts in Mathlib's mixed coordinates
  `InfiniteAdeleRing.ringEquiv_mixedSpace`. The real coordinate of
  `infiniteAdeleEquiv e y` at a real place `w` equals the real coordinate of `y`
  at `realPlace e w`. At a complex place `w`, for all `y` at once, the complex
  coordinate equals the coordinate of `y` at `complexPlace e w` or its complex
  conjugate.

## The compact subgroup

`standardInfiniteCompact K n` is the subgroup of
`GL_n(InfiniteAdeleRing K)` whose matrix at each real place is orthogonal and
whose matrix at each complex place is unitary. Its membership criterion is
`mem_standardInfiniteCompact_iff`.

- `infiniteEquiv_mem_standardInfiniteCompact`: if `g` lies in
  `standardInfiniteCompact K n`, then `AdelicGLTransport.infiniteEquiv n e g`
  lies in `standardInfiniteCompact L n`. At a real place of `L` the transported
  matrix is the matrix of `g` at the corresponding real place of `K`. At a
  complex place it is that matrix or its entrywise conjugate. The private lemma
  `map_star_mem_unitaryGroup` shows that the entrywise conjugate of a unitary
  matrix is unitary.
- `comap_infiniteEquiv_standardInfiniteCompact`: the preimage of
  `standardInfiniteCompact L n` under `infiniteEquiv n e` is exactly
  `standardInfiniteCompact K n`. The reverse inclusion applies the previous
  result to `e.symm` and uses `infiniteEquiv_trans`.
- `compactEquiv n e : standardInfiniteCompact K n ≃* standardInfiniteCompact L n`
  restricts `infiniteEquiv n e`. Its inverse is the restriction of
  `infiniteEquiv n e.symm`. `compactEquiv_val` gives the underlying matrix.
  `compactEquiv_refl`, `compactEquiv_trans` (covariant composition through a
  third field `M`), `compactEquiv_apply_symm` and `compactEquiv_symm_apply` give
  the identity, composition and inverse laws.

The module puts no topology on `compactEquiv`. It constructs no transport of
functions, representations or automorphic forms; the consumer
`Langlands.Automorphic.ArithmeticTransportRelation` uses `compactEquiv` only to
compare compact actions.
