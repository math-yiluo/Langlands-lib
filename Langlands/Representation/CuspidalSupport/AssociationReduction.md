# Weyl transport and the reduction of factor matching to adjacent block swaps

Authors: Worker 242.

This module proves that factor matching for associated irreducible cuspidal
inducing data on `GL_n` (the target `AssociatedCuspidalInductionFactorsTheorem`
of `Langlands.Representation.CuspidalSupport.AssociationForwardStatement`)
follows from two ingredients, each supplied as an explicit hypothesis:

1. the adjacent-swap case: factor matching when a minimal Levi-conjugating
   permutation exchanges two neighbouring blocks and fixes all other blocks;
2. transitivity of `HaveSameJordanHolderFactors`.

The case of at most one block, and quasicuspidality of transport along the
canonical block reordering, are proved here outright. The module also
collects general facts about Weyl transport of Levi representations. It
imports the published `BlockPermutation` module and uses the existing
`ConjugatesLevi`, `leviConjugation`, `transport`, `IsLeviCuspidal`,
`IsLeviQuasicuspidal`, `RepresentationsAssociated`,
`HaveSameJordanHolderFactors` and `normalizedParabolicInduced` without
changing them.

## Provenance

The content is internal and derived. The route is the one of
Bernstein–Zelevinsky 1977 (registered source
`bernstein-zelevinsky-1977-induced-i`), §2.16(2) and §2.17, printed p. 450:
for `GL_n` every Weyl element relating two associated standard Levis is a
product of elementary maps, each of which transposes two neighbouring blocks,
and factor matching is propagated along such a product by transitivity. Here
that decomposition is the generation of the symmetric group on block labels by
adjacent transpositions (Mathlib's `Equiv.Perm.mclosure_swap_castSucc_succ`).
The single-block case uses that the one-block parabolic is the whole group.
The adjacent-swap case and transitivity are not proved here; they are
hypotheses of the final theorem.

## Weyl transport

- `leviConjugation_symm_symm` and `transport_transport`: for
  `hw : ConjugatesLevi B C w`, `hv : ConjugatesLevi C D v` and
  `hu : ConjugatesLevi B D u` with `v * w = u`, the inverse conjugations
  compose, and `transport C D v hv (transport B C w hw ρ) = transport B D u hu ρ`.
  The proof checks equality after the injective Levi embedding, using
  `leviConjugation_symm_embedding` and multiplicativity of
  `GeneralLinear.permutation`.
- `transportEquiv`: an actual equivalence `ρ ≃ σ` of Levi representations is
  also an equivalence of their transports (same linear equivalence).
- `weylLeviElement b hb`: for `b ∈ blockWeyl B`, the permutation matrix of `b`
  lies in the embedded Levi (`permutation_mem_levi_iff`), and this is the
  corresponding Levi element. `leviConjugation_symm_weyl` shows that
  self-conjugation of the Levi by `b` is conjugation by this element, and
  `transportWeylEquiv` is the resulting equivalence
  `transport B B b hb' ρ ≃ ρ`, given by the action of the element.
- `subrepresentationCompOrderIso`, `isIrreducible_comp_iff`,
  `isIrreducible_comp_mulEquiv_iff`: pulling back along a surjective monoid
  homomorphism does not change the lattice of invariant subspaces, so it
  preserves and reflects irreducibility. Hence `isIrreducible_transport`.
- `leviConjugationContinuous`: Levi conjugation as an equivalence of
  topological groups (from `continuous_leviConjugation` and its inverse);
  `isAdmissible_transport` then follows from the published
  `isAdmissible_comp_continuousMulEquiv`.

## Transport along the canonical block reordering

Write `L` for `leviConjugation B (B.permute e) (B.blockPermutation e) h`.

- `leviConjugation_blockPermutation_apply`: `L m i = m (e i)`; conjugation by
  the canonical reordering just reorders the Levi factors. The proof compares
  matrix entries of the embedded block diagonals, using
  `permutation_conjugate_entry` and `blockPermutation_symm_index`.
  `leviConjugation_symm_blockPermutation_apply` is the inverse form
  `L.symm m (e i) = m i`.
- `map_pi_blockPermutation`: for any blockwise choice `K` of subgroups of the
  `GL_m` attached to block shapes, the preimage under `L` of the product of
  the `K (S i)` over a refinement `S` of `B.permute e` is the product over the
  reindexed refinement `Equiv.piCongrLeft _ e S` of `B` (whose block `e i` is
  `S i`). It applies to the refined parabolic and the refined unipotent radical.
- `isLeviQuasicuspidal_transport_blockPermutation`: if `ρ` is quasicuspidal on
  the Levi of `B`, its transport to `B.permute e` is quasicuspidal. A proper
  refinement of `B.permute e` corresponds to a proper refinement of `B`, and
  the published `Jacquet.coinvariantsMapEquiv` identifies the coinvariants of
  the transport under the refined unipotent radical with the coinvariants of
  `ρ` under the corresponding radical of `B`, which vanish.

## Adjacent transpositions

`closure_adjacent_swaps L` shows that the transpositions of `j` and `j + 1`
(`j + 1 < L`) generate `Equiv.Perm (Fin L)` as a monoid, by comparison with
`Equiv.Perm.mclosure_swap_castSucc_succ` (and trivially for `L = 0`).
`val_swap_adjacent` computes such a transposition on natural-number values.

## Length-one series

For a complex representation `A` of a group, `lengthOneFiltration A` is the
filtration `0 ⊆ A` built with `ObjectRepFiltration.ofSubrepresentations`.
`lengthOneGradedMap A` sends `v` to the class of `v` in its only graded piece;
it is injective because the lower step is zero and surjective because the
graded projection is, so `lengthOneGradedEquiv A` is an actual equivalence
between `A` and that graded piece.
`haveSameJordanHolderFactors_of_isIrreducible`: if `A` is irreducible and
`A ≃ A'` (carriers in independent universes), then both length-one series
have simple factors (irreducibility transported along equivalences by the
published `isIrreducible_iff_of_equiv`) and their graded pieces are
equivalent, so `HaveSameJordanHolderFactors A A'`.

## At most one block

- `length_pos_of_pos`: a block shape of positive rank has at least one block.
- `eq_of_length_eq_one`: two one-block shapes of the same rank are equal (the
  sole block has size `n`, by the published `singleBlock_size`).
- `isIrreducible_normalizedParabolicInduced_singleBlock`: if `B` has one block
  and `σ` is smooth and irreducible, then `T.normalizedParabolicInduced B σ`
  is irreducible. The parabolic is the whole group
  (`singleBlock_parabolic_eq_top`). The inducing representation of the
  parabolic is the half-modulus twist of the inflation of `σ`; precomposing
  it with the corestriction `GL_n → P` gives a smooth representation of
  `GL_n`, and the published `fullInductionEquiv` identifies the induced
  representation with it. Irreducibility passes through the surjective
  corestriction, the twist (`isIrreducible_twist_iff`) and the surjective Levi
  projection.
- `associatedCuspidalInductionFactors_of_length_lt_two`: the target statement
  when `B.length < 2`. Then `B` has exactly one block; the block map of the
  conjugating permutation `w` (`exists_blockMap_of_conjugatesLevi`) forces
  `C` to have one block, so `C = B`. Every permutation then preserves the
  unique block, so `transport B B w hw σ ≃ σ` (`transportWeylEquiv`) and hence
  `σ ≃ τ`. Normalized induction of this equivalence
  (`normalizedParabolicInducedEquiv`) and irreducibility of the induced
  representation give the conclusion through the length-one series.

## The reduction

Fix `p`, `F`, `T` and `n`. The adjacent-swap hypothesis has exactly the shape
of the proposition specified in statement task `c5bec005`: for
`hw : ConjugatesLevi B C w` with `j + 1 < B.length`, block map
`(blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)`,
`IsMinimalRepresentative B C w`, irreducible Levi-cuspidal `σ` and `τ` and
`transport B C w hw σ ≃ τ`, it concludes `HaveSameJordanHolderFactors` of the
two normalized inductions. Transitivity is assumed for representations of
`GL_n(F)` in the relevant carrier universes.

- `factors_step`: let `P(e)` say that factor matching holds for every minimal
  conjugating `w` whose block map is `e.symm` (in natural-number form), for
  every irreducible cuspidal `σ` and every irreducible cuspidal `τ` equivalent
  to the transport. From `P(e)` with targets in the source carrier universe,
  `P(e * s)` follows for an adjacent transposition `s` and targets in an
  arbitrary universe. Proof: put `B' = B.permute e` and
  `w' = B.blockPermutation e`, which is minimal and conjugating, with block map
  `e.symm` (`BlockPermutation`). Then `v = w * w'⁻¹` has block map `s`, so it
  conjugates `B'` onto `C` (`conjugatesLevi_of_blockIndex`) and is minimal
  (`isMinimalRepresentative_mul_inv`). The transport `σ'` of `σ` to `B'` is
  irreducible and cuspidal (admissibility by `isAdmissible_transport`,
  quasicuspidality by `isLeviQuasicuspidal_transport_blockPermutation`). `P(e)` matches `σ` with `σ'`; since
  `transport B' C v (transport B B' w' σ) = transport B C w σ ≃ τ`
  (`transport_transport`), the adjacent-swap hypothesis matches `σ'` with
  `τ`; transitivity concludes.
- `factors_of_blockMap`: when `B.length ≥ 2`, `P(e)` holds for every `e`
  (targets in the source universe), by
  `Submonoid.induction_of_closure_eq_top_right` with `closure_adjacent_swaps`.
  For an adjacent transposition `s₀`, `P(s₀)` is the adjacent-swap
  hypothesis, and `P(1)` follows from it by `factors_step` since `s₀ * s₀ = 1`.
- `associatedCuspidalInductionFactors_of_adjacent`: the full target statement
  for the fixed `F`, `T`, `n` with `0 < n`, from the two hypotheses (each is
  taken once with target universe `uV` and once with `uW`). If `B.length < 2` it is the case above.
  Otherwise write the associating `w` as `v * b` with `v` a minimal conjugating
  permutation and `b ∈ blockWeyl B` (the published `minimalConjugatingCosets`).
  Then `transport B C v σ ≃ transport B C w σ ≃ τ` by `transportWeylEquiv`,
  `transportEquiv` and `transport_transport`. Let `e` be the block map of `v`
  (`exists_blockMap_of_conjugatesLevi`). Writing `e = (e * s₀) * s₀`,
  `factors_of_blockMap` gives `P(e * s₀)` in the source universe and
  `factors_step` gives the conclusion for `τ` in its own universe.

The shared `transportEquiv` construction is imported from
[`LeviAssociation`](LeviAssociation.md); it retains the same underlying linear
equivalence and inverse-conjugation action.
