# Fibre products of schemes over an algebraic space

Helper module for the proof of `ProperSchemeCoverStatement` (weak Chow lemma route).

## Declarations

- `spacePullback a b`, `spacePullbackFst a b`, `spacePullbackSnd a b`: for maps
  `a : h_U ⟶ X` and `b : h_V ⟶ X` from schemes over `S` to an algebraic space `X`, the scheme
  `U ×_X V` over `S` representing their fibre product (it exists because the diagonal of `X` is
  representable, `AlgebraicSpace.representable_from_scheme`), with its two projections.
- `spacePullback_isPullback`, `spacePullback_w`: the represented square is a pullback square of
  presheaves, and in particular commutes.
- `spacePullbackLift`, `spacePullbackLift_fst`, `spacePullbackLift_snd`,
  `spacePullback_hom_ext`: the universal property for morphisms from schemes over `S`.
- `spacePullbackLift_mem_of_relative_diag`: if every represented base change of the diagonal of
  `X` lies in a property `P` of monomorphisms that respects isomorphisms, then the pairing
  `U ×_X V ⟶ U ×_S V` of the two projections lies in `P`.
- `isClosedImmersion_spacePullbackLift`: if `X` is separated, this pairing is a closed immersion.
- `etale_spacePullbackFst`, `etale_spacePullbackSnd`, `surjective_spacePullbackFst`,
  `surjective_spacePullbackSnd`: a projection is étale (surjective) when the opposite map is
  étale (surjective).

## Proof

The statements and proofs generalize, from the base `Spec K` of a field to an arbitrary base
scheme `S`, the library's `pairPullback` construction and
`pairPullbackLift_mem_of_relative_diag` (module `EtaleChartLocalSeparation`). The equalizer of the
two maps `h_{U ×_S V} ⟶ X` is cut out by a morphism `ι : Z ⟶ U ×_S V` in `P`
(`exists_representsEqualizer_of_relative_diag`). The pairing factors through `ι`, the point of
`U ×_X V` given by `ι` composed with the two product projections is inverse to that factorization,
and `P` respects isomorphisms. The étale and surjective statements are the defining properties of
étale and surjective maps of presheaves applied to the represented square.
