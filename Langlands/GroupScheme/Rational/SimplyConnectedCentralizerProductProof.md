# Proof: `G(k) = G(k)^♮ · Z_G(S)(k)` (KP Fact 2.6.22, minimal Levi case)

Author: Worker 4674.

This module proves the published statement
`Langlands.GroupScheme.SimplyConnectedCentralizerProductStatement` of
[`SimplyConnectedCentralizerProductStatement`](SimplyConnectedCentralizerProductStatement.md)
at an arbitrary universe `u`, as the theorem
`Langlands.GroupScheme.simplyConnectedCentralizerProduct`. The statement is
Kaletha–Prasad, Fact 2.6.22, for the minimal Levi subgroup `Z_G(S)`, over an arbitrary
field. Its Markdown explains how the formal statement relates to the source.

The theorem uses no hypothesis beyond those of the statement. There is no restriction on
the field: no valuation, completeness, perfectness, characteristic, finiteness or
infiniteness assumption. The proof depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The data

The statement supplies a field `k : Type u`, a commutative group scheme `S` and group
schemes `G`, `Z`, `C`, `D` over `Spec k`, together with morphisms `i : S → G`,
`j : Z → G`, `d : D → G` and `π : C → D`. It assumes three things:

- `hcover : IsSimplyConnectedDerivedCover d π`;
- `hi : IsMaximalSplitTorus i`;
- `hj : (torusCentralizer i).IsRepresentedBy j`.

A rational point `g ∈ G(k)` is given. The goal is to find `c ∈ C(k)` and `z ∈ Z(k)` with
`g = rationalPoints.map (π ≫ d) c * rationalPoints.map j z`.

## The proof

The proof composes five published Library results. All of them hold over an arbitrary
field.

1. **Instances.** The field `isConnectedReductive` of `hcover` shows that `G` is
   connected reductive. This gives the instances `IsAffineHom G.X.hom`
   (`IsConnectedReductive.isAffineHom`) and `Smooth G.X.hom`
   (`IsConnectedReductive.smooth`). The closed-immersion part of `hi` gives
   `Mono i.hom.hom.left` (`IsSplitSubtorus.mono`). The published results below take
   these instances as instance arguments. They are definitionally the instances that
   `RootRankOneFactorizationStatement` and `RelativeRootSystemStatement` build with
   `haveI`.

2. **Opposite factor pairs.** The published theorem `rootRankOneFactorization` proves
   `RootRankOneFactorizationStatement`. Applied to `k`, `G`, `S` and `i`, it gives
   `RelativeRoot.HasRankOneFactorization i`. For every relative root `a` and every
   nonidentity rational point `x` of the actual root subgroup of `a`, its first conjunct
   is the unique existence of an opposite factor pair. Keeping only existence gives
   `RelativeRoot.HasOppositeFactorPairs i`. The published
   `relativeRootSystemStatement_of_rootRankOneFactorizationStatement` extracts pair
   existence in the same way.

3. **A generic cocharacter.** `S` is a split torus, by the first component of
   `hi.isSplitSubtorus`. The published `IsSplitTorus.exists_genericCocharacter` therefore
   gives a cocharacter `ν` of `S` with `IsGenericCocharacter i ν`, that is, with nonzero
   pairing against every relative root.

4. **The relative root system and the Bruhat decomposition.** The published theorem
   `relativeRootSystem` proves `RelativeRootSystemStatement`, which gives
   `HasRelativeRootSystem i`. The published theorem `rationalBruhat` proves
   `RationalBruhatStatement`. Applied to `ν` and its genericity, it gives
   `HasRationalBruhatDecomposition i ν`.

5. **Assembly.** The published theorem
   `exists_derivedCover_mul_centralizer_of_oppositeFactorPairs` (module
   [`DerivedCoverWeylLift`](DerivedCoverWeylLift.md)) takes `j`, `hcover`, `hi`, `hj`,
   opposite-pair existence, the root-system realization, the generic cocharacter `ν` with
   its genericity, and the Bruhat decomposition for `ν`. For every `g ∈ G(k)` it returns
   the required points `c ∈ C(k)` and `z ∈ Z(k)`. Applying it to `g` closes the goal.

The module itself only verifies that the premises of step 5 are discharged by the
published results of steps 1–4. The mathematical content lies in those published results.
In outline, `exists_derivedCover_mul_centralizer_of_oppositeFactorPairs` proceeds as
follows; its Markdown describes the full argument.

- The published `genericCentralizer` identifies the dynamic centralizer of `ν ≫ i` with
  `Z_G(S)`.
- The rational points of the contracting unipotent subgroup `U_G(ν)` lie in the image
  of `C(k) → G(k)` (`Dynamic.unipotentPoints_le_derivedCoverImage_of_reflectionData`).
- Every relative-Weyl class has a representative in that image
  (`subgroupRelativeWeylMap_derivedCover_surjective`). These representatives come from
  normalizing products of opposite root points, which lie in the image of `C(k)`.
- The Bruhat covering `G(k) = ⋃ P(k) n P(k)` is rewritten as `U(k) N(k) U(k) Z(k)`.
  Each normalizer point `n` is a cover-image point times a centralizer point. This gives
  the product `G(k) = G(k)^♮ · Z_G(S)(k)` (`exists_cover_mul_centralizer_of_bruhat`, module
  [`SimplyConnectedCentralizerProductReduction`](SimplyConnectedCentralizerProductReduction.md)).
- The centralizer factor is lifted to `Z(k)` through `hj`.

## Relation to the source proof

Kaletha–Prasad prove Fact 2.6.22 with three inputs: the Bruhat decomposition (Borel,
*Linear Algebraic Groups*, 21.15), the fact that root groups lie in `G(k)^♮`, and the
equality of the relative Weyl groups of `G` and of its simply connected cover. The
implemented proof uses the same three ingredients in the following forms:

- the published rational Bruhat decomposition `rationalBruhat`;
- the published lifting of contracting unipotent points into the image of `C(k)`;
- the published surjectivity of the restricted relative-Weyl map from that image.

It does not use the comparison of the two relative Weyl groups. The image of `C(k)`
already contains a representative of each relative-Weyl class of `G`. The source works
over a Henselian discretely valued field. As the statement's Markdown records, the
argument and this proof hold over every field.

Sources:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 2.6.20 and
  Fact 2.6.22, printed p.104/PDF p.135. Registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
