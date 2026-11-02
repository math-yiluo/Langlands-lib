# Proof: separated commutative group spaces over a field are schemes

`separatedAddCommGroupSheafSchemeRepresentability` proves
`SeparatedAddCommGroupSheafSchemeRepresentabilityStatement.{u}` for every universe `u`. Let
`k` be a field and `H` an fppf sheaf on schemes over `Spec k` that is an algebraic space
(`IsAlgebraicSpace`) and is isomorphic to the underlying presheaf of a presheaf `G` of
commutative groups. Suppose its diagonal is a closed immersion and it has an etale surjective
atlas from a scheme locally of finite type over `k`. Then `H` is represented by a scheme `P`
that is separated and locally of finite type over `k` (Stacks, Groupoids in Spaces,
Lemma 79.10.2, commutative case).

The proof is one line: it applies
`separatedAddCommGroupSheafSchemeRepresentability_of` (module
`SeparatedAddCommGroupSheafSchemeRepresentabilityReduction`, whose Markdown describes the
construction) to `finiteLocallyFreeEquivalenceRelationAffineQuotient`, the Library proof of
`FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement` (Stacks 03BM).

Outline of the construction behind the reduction. Write `F := G ⋙ forget` and
`G_L := F × Spec L`.

1. Dense affine opens, for affine atlases only (`SeparatedDenseAffineOpenReduction`).
   `separatedDenseAffineOpenLFT_of` proves `SeparatedDenseAffineOpenLFTProp`. Let `X` be a
   separated algebraic space over `k` with an etale surjective atlas from an *affine* scheme
   `U` locally of finite type. Then `X` has an open subspace represented by an affine scheme
   locally of finite type, whose preimage in `U` is dense. Proof: the atlas relation is etale.
   Its finite locus is invariant (`FiniteLocusInvariant`) and contains the finitely many
   generic points of `U` (`FiniteLocus`). Finite-set 03JE
   (`FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenProof`) gives an invariant affine
   open, and 03BM gives its affine quotient.

   The affine-atlas hypothesis is essential. The proof never applies this step to `H` or to
   a whole base change `G_L`, which in general have no dense affine open. For example, the
   constant group scheme `∐_{n ∈ ℤ} Spec k` satisfies the hypotheses of the theorem, but its
   only dense open is itself, which is not quasi-compact.
2. Charts through field points (`GroupLocalCharts.exists_open_chart_of_field_point`). Let
   `K/k` be finite and `t` a `K`-point of the atlas. Choose `L ⊇ K` finite and normal over
   `k`, and an affine open `U₁` of the atlas containing the image of `t`. Then
   `U₀ := U₁ × Spec L` is an affine etale chart `a₀` of `G_L`. Let `g_L` be the pullback of
   `t^* a` to `Spec L`.
   - Step 1 (`exists_affine_containing_translates`): the finite coproduct
     `V = ∐_{τ ∈ Aut(L/k)} U₀` carries an etale map `b` to `G_L`, whose `τ`-th component is
     the translate of `a₀` by `(Spec τ)^* g_L`. The sheafified image `Q` of `b` is an open
     subspace of `G_L`. It is a separated algebraic space with the affine etale surjective
     atlas `V`. Step 1 applies to `Q`, not to `G_L`, and gives an affine open `A ⊆ Q`, locally
     of finite type. A closed point in the intersection of the dense preimages of `A` in
     the components yields a finite normal extension `L'/k` and an `L'`-point of `U₀` all of
     whose translates lie in `A`.
   - Step 2 (`exists_galois_stable_affine`): intersecting the transported copies of `A` over
     `σ ∈ Aut(L'/k)` gives an affine open `W ⊆ F × Spec L'`, locally of finite type, that is
     Galois stable and contains the pullback of `g_L` to `Spec L'`.
   - Step 3: by Galois stability, membership in `W` depends only on the `F`-component
     (`fst_invariant_of_galois_stable`). `isLFTAffineOpen_universalImage_fst`
     (`GaloisAffineDescent`, using 03BM) descends `W` along `Spec L' → Spec k` to an affine
     open `W₀ ⊆ F`. `W₀` is locally of finite type by `FiniteFlatSourceDescent`, and it
     contains `t^* a` because `Spec L' → Spec K` is surjective.
3. Gluing (`ClosedPointChartRepresentability`): these charts cover the canonical points of
   the closed points of the atlas, hence form an open cover. They glue to a scheme `P`
   representing `H`. `P` is separated because the diagonal is closed, and it is locally of
   finite type because each chart is. The theorem needs no quasi-compactness hypothesis.
