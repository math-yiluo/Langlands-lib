# Proof: real standard-module parameters in a common isotypic module

`realStandardIsotypicParameterUniqueness` proves
`RealStandardIsotypicParameterUniquenessStatement` with both carrier
universes `uV` and `uW` free. Two rank-`n` real block lists `ds` and `es`
are given. Their `O(n)`-finite standard modules inject into a module `W`,
and `W` is isotypic for one irreducible module `(V, ρ, π)`. The theorem
concludes `(realMoeglinData ds).Perm (realMoeglinData es)`. Its proof uses
the irreducibility and isotypy hypotheses, the two rank equalities, and the
two injective intertwiners. It does not use the hypotheses that `(V, ρ, π)`
is a real `(𝔤, K)`-module and is admissible. The statement still carries
both of them.

## Route

The paired statement Markdown cites the Grothendieck-ring argument of
Tadić (2009), Propositions 1.1 and 1.3, pp. 6–7. The Lean proof follows a
different route and does not build virtual characters. It shows that each
standard module is itself irreducible and isomorphic to the common type.
The parameters of the two modules are then compared through the
Library's positive-weight uniqueness theorem, which compares characters on the
elliptic Cartan subgroup.

## Steps of the Lean proof

1. **Normalization.** `NF ds` abbreviates
   `ds.flatMap realBlockNormalize`. It splits each weight-zero induction
   block into its two characters and replaces each negative induced weight
   by its conjugate. The private lemma `realMoeglinData_normalize` proves
   `realMoeglinData (NF ds) = realMoeglinData ds`. Conjugation negates the
   weight and keeps the exponent, so `realBlockMoeglinData` is unchanged by
   `RealBlock.positiveWeight`. The equality then reduces to the Library's
   `realMoeglinData_flatMap_expand`. The Library also gives
   `realRank (NF ds) = realRank ds` (`realRank_flatMap_normalize`) and the
   positivity of every induced weight in `NF ds`
   (`weight_pos_of_mem_flatMap_normalize`).

2. **Embedding the normalized model.** Normalization does not change the
   standard module as a space of functions
   (`realStandardModule_flatMap_normalize`). Applying
   `RealInjectiveIntertwinerExists.of_eq` to the identity intertwiner
   `RealInjectiveIntertwinerExists.refl` gives an injective standard
   intertwiner from the normalized model to the original one. The private
   lemma `normalized_embedding` composes it with the given injective
   intertwiner into `W`. The composite is again an injective member of
   `gkHoms` into `(W, σ, ξ)`.

3. **Each standard module is the common type.** The private lemma
   `standard_equiv_of_isotypic` takes a rank-correct list with an injective
   `(𝔤, K)`-map into the isotypic module. The compact multiplicity-one theorem
   `RealStandardCompactMultiplicityOne.realStandardExistsCompactScalarVector`
   supplies a nonzero vector that every compact-equivariant endomorphism
   scales. `isIrreducibleGKModule_of_injective_of_isotypic` then makes the
   standard module an irreducible `(𝔤, K)`-module. Both irreducible modules
   become irreducible representations of the free monoid on `K ⊕ L`
   (`gkFreeRepresentation`, `isIrreducible_gkFreeRepresentation`). The
   injective map becomes a nonzero intertwining map
   (`gkHomsIntertwiningMap`). `isGKIsotypic_iff` and
   `IsotypicEmbedding.exists_intertwiningMap_ne_zero_of_isotypic` give a
   nonzero intertwining map from the standard module to `(V, ρ, π)`.
   Schur's lemma for irreducible representations
   (`Representation.IsIrreducible.bijective_or_eq_zero`) makes this map
   bijective, so it is an equivalence of free-monoid representations.

4. **A bijective intertwiner between the normalized modules.** Step 3
   applies to `NF ds` and `NF es` and the embeddings of step 2. Composing
   the first equivalence with the inverse of the second gives a bijective
   linear map `T` between the two normalized standard modules. By
   `toLinearMap_mem_gkHoms`, `T` lies in `gkHoms`. The private lemma
   `isRealStandardIntertwiner_of_mem_gkHoms` turns it into an
   `IsRealStandardIntertwiner` through
   `InductionStages.isRealStandardIntertwiner_iff`. The compact condition
   is read at `InductionStages.toUnitary n k` and the Lie condition at
   `1 ⊗ₜ X`.

5. **Positive-weight uniqueness.** `RealPositiveWeightStandardUniqueStatement`
   applies to `NF ds` and `NF es`. They have rank `n` and positive induced
   weights, both modules are irreducible by step 3, and `T` is bijective.
   It gives `(NF ds).Perm (NF es)`. `List.Perm.flatMap_right` applied to
   `realBlockMoeglinData` gives a permutation of the Mœglin data. Rewriting
   with step 1 gives the conclusion for `ds` and `es`. The private lemma
   `uniqueness_of_positiveWeightUnique` performs steps 4 and 5 from any
   proof of positive-weight uniqueness.

6. **Assembly.** The Library's `realStandardEllipticCartanReduction` proves
   that `RealStandardEllipticCartanComparisonStatement` implies
   positive-weight uniqueness.
   `RealStandardEllipticCartan.realStandardEllipticCartanComparison`, in
   `Langlands.Representation.Archimedean.RealStandardEllipticCartanComparisonProof`,
   proves the comparison. The main theorem applies
   `uniqueness_of_positiveWeightUnique` to this composite.

## Provenance

The proof is internal. It assembles published Library results, and its
private lemmas are bookkeeping for the normalization, the free-monoid
encoding and Schur's lemma. The normalization is the one in the statement's
Markdown. It follows Knapp (1994), `knapp-1994-archimedean-llc`, (2.1)–(2.4)
and Theorem 1(c), pp. 399–400 (one-based PDF pp. 409–410), and the
weight-zero decomposition on p. 402 (one-based PDF p. 412). The Markdown of
`RealStandardEllipticCartanReduction` gives the sources for the
elliptic-Cartan character comparison. It cites Knapp's *Representation
Theory of Semisimple Groups*, Chapter X, (10.21) on p. 348, (10.27) on p. 352,
Proposition 10.19 on p. 353 and Corollary 10.13 on pp. 343–344. The
statement's Markdown describes the paper route through Tadić (2009),
`tadic-2009-gl-n-c-gl-n-r-unitary-duals`, Section 1, Propositions 1.1 and
1.3, pp. 6–7 of the author's PDF. The Lean proof reaches the same
conclusion without the Grothendieck ring. Instead of comparing positive
multiples of one irreducible class, it uses compact multiplicity one to
show that each standard module is isomorphic to the common irreducible
type.
