# Unitary central characters and nontrivial Jacquet modules along sub and quotient maps

This internal unit supports the proof task on the unitarizable-constituent step of
Renard, Théorème VII.1.3. Its provenance is the published constructions it combines:
the Library's `UnitaryCentralCharacter` structure,
`isNormalizedJacquetExponent_iff_isOpen_ker_and`,
`normalizedJacquetFunctor_map_injective`,
`isLimitOfCompactSubgroups_pointImage_radical`,
`Jacquet.Localization.mk_surjective` and `normalizedJacquetFunctor_map_mk`. It
asserts no new source translation. It is the exactness input used in Renard's proof:
for a subrepresentation or quotient `π₁` of `π`, a nonzero `r_Q π₁` forces a nonzero
`r_Q π` (VI.1.2, exactness of the Jacquet functor).

## Central characters

For a group `Γ` with a topology and smooth complex representations `A` and `B` of
`Γ`:

- `unitaryCentralCharacterOfInjective` restricts a unitary central character of `B`
  along a morphism `f : A ⟶ B` with injective underlying map. The character is the
  same. The action identity on `A` follows from that on `B` by injectivity and
  equivariance.
- `unitaryCentralCharacterOfSurjective` carries a unitary central character of `A`
  to `B` along a morphism `f : A ⟶ B` with surjective underlying map. Each vector of
  `B` has a preimage, and the action identity is pushed through `f`.

No topology on `Γ` beyond the one in `UnitaryCentralCharacter` is used.

## Jacquet modules

Fix an actual represented parabolic `p : P ⟶ G` with rational Levi `l`, geometric
unipotent radical `r` and multiplication isomorphism. Here `G(k)` carries the canonical
point topology, assumed locally compact and nonarchimedean. `jacquetFunctor` is the
published normalized Jacquet functor of this data.

- `nontrivial_jacquet_of_isNormalizedJacquetExponent`: if `χ` is a normalized Jacquet
  exponent of `π` along `(p, l, r, a)` for a split component `a`, then the Jacquet
  module of `π` is nontrivial. The published criterion says that the weight space of
  `χ` is not `⊥`. On a subsingleton carrier every subrepresentation is `⊥`.
- `nontrivial_jacquet_of_injective`: for `f : W ⟶ π` with injective underlying map,
  nontriviality of the Jacquet module of `W` implies that of `π`. The published
  `normalizedJacquetFunctor_map_injective` makes the Jacquet map injective, using that
  the radical's point image is a limit of compact subgroups
  (`isLimitOfCompactSubgroups_pointImage_radical`). This theorem additionally assumes
  that `k` is a nonarchimedean local field (`ValuativeRel k`,
  `IsNonarchimedeanLocalField k`), as that lemma requires.
- `nontrivial_jacquet_of_surjective`: for `f : π ⟶ W` with surjective underlying map,
  nontriviality of the Jacquet module of `W` implies that of `π`. Every Jacquet class
  of `W` is the class of some vector `f x`, by surjectivity of the quotient map. The
  class of `f x` is the image of the class of `x`, so the Jacquet map is surjective.

The other statements need only a Hausdorff topological field `k` and an affine
ambient group. No admissibility, finite generation or reductivity is assumed.
Exponents themselves are not transferred along quotients, which would need the
generalized-eigenspace decomposition. Only nontriviality is transferred.
