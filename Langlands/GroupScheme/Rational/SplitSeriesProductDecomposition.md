# Product decomposition along one step of a split series

This helper module serves the proof of
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`
(task 6b07dcd2-af39-4c69-8ade-d0faa997a49f). Take one step K ⟶ H ⟶ V of a split
series of an affine group H over Spec R, with V a one-dimensional vector group.
Then the quotient map H ⟶ V has a section that preserves the unit, and the map
(κ, t) ↦ j(κ) · s(t) identifies K ⊗ V with H as schemes over Spec R. This is
the standard fact that a split-unipotent group is an affine space as a scheme,
in the one-step form the proof needs. The argument was worked out for this
formalization; it does not follow a particular cited text.

Everything is in the namespace `Langlands.GroupScheme.SplitSeriesDecomposition`.

## Categorical lemmas

Let C be a cartesian monoidal category, and let H and V be group objects in C.
Products of morphisms below are the pointwise products of the group objects.

- `exists_unit_section`: let q : H ⟶ V be a monoid homomorphism and s a
  section of q (s ≫ q = 𝟙 V). Then s' := s · (const (η ≫ s))⁻¹ is again a
  section of q, and η[V] ≫ s' = η[H]. Here const (η ≫ s) is the composite
  V ⟶ 𝟙_ ⟶ V ⟶ H.
- `isIso_mul_of_section`: let j : K ⟶ H be a monomorphism and q : H ⟶ V a
  monoid homomorphism with j ≫ q = 1. Let s be a section of q. Assume that
  every point x of H with x ≫ q = 1 factors through j. Then
  (fst ≫ j) · (snd ≫ s) : K ⊗ V ⟶ H is an isomorphism. The point
  𝟙 · (q ≫ s)⁻¹ of H maps to 1 under q, so it factors as r ≫ j for some
  r : H ⟶ K. The inverse is lift r q. The two composites are the identity:
  after the map, q recovers snd, and r recovers fst (checked after
  cancelling the monomorphism j).

## One step of a split series

Fix R : CommRingCat.

- `exists_section_isIso_mul`: let j : K ⟶ H be a closed subgroup and let
  q : H ⟶ V be an fppf quotient of H by the range of j. Assume V is a vector
  group of dimension 1, K has a split series of some length n, and H.X is
  affine over Spec R. Then there is a section s : V.X ⟶ H.X of q with
  η[V.X] ≫ s = η[H.X] such that (fst ≫ j) · (snd ≫ s) : K.X ⊗ V.X ⟶ H.X is an
  isomorphism.

  The proof uses the Library's torsor results. Cocycles of K vanish over
  affine schemes, by `SplitUnipotentAffineTorsor.cocyclesVanish_of_hasSplitSeries`
  with the one-dimensional vector-group case
  `Cocycle.isTrivial_of_isVectorGroupOfDimension_one`. So
  `SplitUnipotentAffineTorsor.exists_section` gives a section σ of q.
  `exists_unit_section` normalizes it to s. `isIso_mul_of_section` gives the
  isomorphism. Its two kernel hypotheses come from
  `SplitUnipotentAffineTorsor.comp_comp_eq_one` and
  `SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one`.

- `HasSplitSeries.exists_iso_tensor`: let H have a split series of length
  n + 1, with H.X affine over Spec R. Then there are groups K and V with an
  isomorphism K.X ⊗ V.X ≅ H.X of schemes over Spec R. Here K has a split series
  of length n, V is a vector group of dimension 1, and K.X is affine over
  Spec R. The proof applies `exists_section_isIso_mul` to the first step of
  the series. K.X is affine over Spec R because j is a closed immersion over
  H.X.
