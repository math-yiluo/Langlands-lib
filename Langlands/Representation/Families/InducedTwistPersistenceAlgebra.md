# Algebraic helpers for the persistence of the inducing exponent

Author: Worker 5120.

This module proves general facts about generalized eigencharacters, finite length and
divisibility. They are used by the persistence modules
`InducedTwistPersistence{Endpoints,Wall,Pieces,Genericity}`. All declarations are in
`Langlands.InducedTwistPersistence`. The module contains no representation-theoretic
hypothesis and no statement to be proved later.

## Exponents along intertwiners

Here `ι : A →* M` is a group homomorphism, and `π`, `σ` are complex representations of `M`
on spaces in independent universes. An exponent of `π.comp ι` is a character `χ` of `A`
with `IsGeneralizedEigencharacter (π.comp ι) χ`.

- `restrictComp ι f` is an intertwiner `f : π → σ`, viewed as an intertwiner
  `π.comp ι → σ.comp ι`. It has the same linear map (`restrictComp_apply`).
- `isGeneralizedEigencharacter_of_injective`: an injective intertwiner `π → σ` carries every
  exponent of `π.comp ι` to an exponent of `σ.comp ι`. The image of a nonzero generalized
  eigenvector is nonzero, and the published `isGeneralizedEigencharacter_of_map_ne_zero`
  applies.
- `isGeneralizedEigencharacter_of_injective_of_mem`: suppose `f` is injective and
  `(σ(ι a) - χ(a))^d` kills `f v` for every `a` and some `v ≠ 0`. Then `χ` is an exponent
  of `π.comp ι`. The proof commutes `f` with these operators by induction on the power.

## Irreducible subrepresentations with a prescribed exponent

`exists_irreducible_sub_isGeneralizedEigencharacter`. Let `G` be a weakly locally compact
nonarchimedean group and `ι : A →* G` a homomorphism into the centre. Let `X` be a smooth
representation of finite length with an exponent `χ` of `X.comp ι`. Then `X` has an
irreducible subrepresentation `C ↪ X` on which `χ` is still an exponent.

The proof takes the published generalized weight space of `χ`. It is nonzero
(`generalizedWeightSpace_ne_bot_iff`) and invariant, because `ι` is central, and as a
subrepresentation it has finite length. The published
`Classification.SegmentHeadSupport.exists_irreducible_subrepresentation` gives an
irreducible subrepresentation of it. A nonzero vector of that subrepresentation lies in
the weight space, and the previous lemma transfers the exponent.

## Finite length and divisibility

- `hasFiniteLength_of_hasSimpleFactors`: a smooth representation with a filtration whose
  graded pieces are simple has finite length. This is the published
  `LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength`.
- `exists_pow_eq_units_pi`: every element of `ι → ℂˣ` has an `n`-th root for `n ≠ 0`,
  because `ℂ` is algebraically closed.
- `exists_pow_eq_of_mulEquiv`: a commutative group with a multiplicative equivalence to
  `ι → ℂˣ` is divisible. It is applied to the published coordinates
  `rationalCanonicalUnramifiedCharacterCoordinates` of the unramified characters.

## Provenance

The module is internal: elementary linear algebra and published Library results, with no
literature assertion of its own. The facts are standard, for example the existence of an
irreducible subrepresentation in a finite-length module with a given central exponent.
