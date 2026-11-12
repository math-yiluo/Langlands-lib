# Almost simplicity reflected through central isogenies

This is derived internal group-scheme infrastructure for the spin-cover proof
in Task 5397, authored by Worker 97. Its provenance is the composition of the
published interfaces named below; it makes no additional source translation or
classification claim.

`AlmostSimpleCentralIsogenyStatement.{u}` says that for any field `k : Type u`,
a central isogeny `p : D ⟶ C` with almost-simple target and smooth connected
source has almost-simple source. The theorem `almostSimpleCentralIsogeny`
proves this statement, and `IsAlmostSimple.of_isCentralIsogeny` is its directly
usable form. There is no restriction on the characteristic or perfection of
the field. Affineness of the source follows from finiteness of the isogeny and
affineness of the target.

The supporting lemmas use the full functor of points, over every test scheme:

- `hom_eq_one_of_finite_target` kills maps from smooth connected affine field
  groups to finite group schemes, by applying `finiteHom_cancel` to the map
  from the finite group to the terminal group.
- `IsCentral.eq_one_of_hasFiniteCenter` factors a central map through an actual
  representative of the full finite centre and applies the preceding lemma.
- `SubgroupFunctor.range_eq_bot_iff_hom_eq_one` equates a trivial range functor
  with the unit underlying morphism.
- `hom_eq_one_of_comp_eq_one` reflects triviality through a finite map by
  comparing the given homomorphism with the explicit unit homomorphism and
  using `finiteHom_cancel`.
- `isCentral_of_commute_of_epi` uses
  `fieldFixedSubgroupRepresentability` for conjugation by a supplied map. If
  its fixed subgroup contains an epimorphic range, the closed-representative
  criterion
  `SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le`
  makes the fixed subgroup the whole target, which gives centrality.

For the main proof, `IsSemisimple.of_isCentralIsogeny` first gives
semisimplicity of `D`. If `D` were trivial as a group functor, epimorphic
surjectivity of `p` would make `C` trivial, contradicting its noncommutativity.
Thus `IsSemisimple.noncommutative_of_nontrivial` supplies noncommutativity of
`D`.

For a smooth connected closed normal subgroup `j : H ⟶ D`,
`HomImage.exists_image` factors `j ≫ p` through a smooth connected closed
subgroup `e : E ⟶ C`, with flat surjective quasi-compact projection
`q : H ⟶ E`. The commuting square and
`SubgroupFunctor.isNormal_range_of_fpqc_square` make the range of `e`
normal. Almost simplicity of `C` makes that range either trivial or full.

In the trivial case, finite cancellation through `p` makes `j` trivial. In the
full case, evaluation at the identity test point supplies a section of `e`;
therefore `e`, and then `j ≫ p`, are epimorphisms over the base.
`semisimpleNormalIsogenyComplement` supplies a semisimple commuting normal
complement `i : K ⟶ D`, with central-isogeny multiplication `H × K ⟶ D`.
After applying `p`, the complement commutes with the epimorphic image of `H`,
so the fixed-subgroup argument makes `i ≫ p` central in `C`. The full centre
of the semisimple target is finite. The finite-target lemma kills `i ≫ p`,
and finite cancellation through `p` kills `i`. Multiplication consequently
takes values in the closed subgroup represented by `j`. Its epimorphic range
forces that closed subgroup to be all of `D`. This proves the required normal
subgroup dichotomy.

This unit establishes the general transfer needed for spin covers. It does not
assert smoothness, almost simplicity or a split-rank computation for any
particular quaternionic isometry group.
