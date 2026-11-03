# Pseudo-parabolic subgroups of actual group schemes

This module defines `Langlands.GroupScheme.IsPseudoParabolicSubgroup` for
homomorphisms `i : P ⟶ G` of actual group schemes over
`Spec (CommRingCat.of k)`, for every field `k : Type u` and arbitrary universe
`u`. The proposition explicitly requires the ambient group `G` to be smooth,
connected and affine. Its product presentation uses a ground-field unipotent
radical and the existing all-test dynamic parabolic.

## Original source and correspondence

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Definition 2.2.1 and Example 2.2.2 are on printed p.62 (PDF p.88); the
discussion before Proposition 2.2.4 is on printed p.63 (PDF p.89).

Definition 2.2.1 specifies pseudo-parabolic subgroups of a smooth connected
affine group over a field as `P_G(λ) R_{u,k}(G)`, for a ground-field
homomorphism from the multiplicative group. The Lean definition retains
these ambient hypotheses and takes
`χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G`, using the Library's actual
multiplicative group scheme. Lean uses `χ` for the source's `λ`.
`Dynamic.parabolic χ` is the existing subgroup
functor defined by extension of the conjugation orbit to the affine line on
every relative scheme test.

The radical factor is essential. Example 2.2.2 explains that it must be
included for general smooth connected affine groups, even when the dynamic
parabolic alone is smaller. No reductivity or pseudo-reductivity hypothesis
is imposed here.

The discussion on printed p.63 introduces the split ground-field radical
`R_{us,k}(G)` and states a separate structural comparison in Proposition
2.2.4. This module uses `R_{u,k}(G)` as in Definition 2.2.1 and does not
replace it by the split radical. The following notions remain distinct over
imperfect fields:

1. The ground-field radical is a greatest smooth connected unipotent normal
   closed subgroup over `k`, expressed by `IsUnipotentRadical`.
2. The split ground-field radical uses greatestness among split competitors,
   expressed separately by `IsSplitUnipotentRadical` and the existing
   `RelativeRoot.IsSplitUnipotent` finite-series predicate.
3. The geometric radical is formed after base change to an algebraic closure.
   The definition here does not identify it with the ground-field radical
   after base change.

## Definition and all-test product

`IsPseudoParabolicSubgroup i` is a `Prop`-valued structure with four fields:

- `smooth : Smooth G.X.hom`;
- `connectedSpace : ConnectedSpace G.X.left`;
- `isAffineHom : IsAffineHom G.X.hom`;
- `presentation`: there are an actual group scheme `U` over `k`, a
  homomorphism `j : U ⟶ G`, and a cocharacter `χ` as above, with
  `IsUnipotentRadical j` and
  `(Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range j) i`.

The imported radical predicate requires a closed immersion, smoothness,
connectedness and the existing unipotence of `U`, normality of its all-test
image, and containment of every smooth connected unipotent normal closed
subgroup image over `k`. It characterizes a supplied greatest representative.
It does not choose a radical or assert that every ambient group has one.
The existential radical in `presentation` belongs to the definition of this
particular subgroup predicate.

The imported `SubgroupFunctor.IsFppfProduct` requires `i` to be a closed
subgroup and gives the following equivalence on every
`T : Over (Spec (CommRingCat.of k))`: an actual point `x : T ⟶ G.X`
factors through `i` if and only if there are a relative scheme `V`, a map
`v : V ⟶ T` whose underlying scheme map is flat, surjective and locally
of finite presentation, and points `p,n : V ⟶ G.X` such that

- `p` belongs to `(Dynamic.parabolic χ).carrier V`;
- `n` belongs to `(SubgroupFunctor.range j).carrier V`;
- `v ≫ x = p * n`.

Both test schemes range over all relative schemes, including nonaffine and
nonreduced ones. This is the internal fppf-image formulation of the subgroup
product in CGP. For represented factors, it expresses local lifting along
multiplication from their scheme product; a family of fppf covering maps can
be combined into one disjoint-union cover. The imported product module
explains this formulation and its limits. No factorization on the original
test is required, and no pointwise subgroup join is used. This module
supplies neither a product-representability theorem nor a comparison theorem
with another construction of an algebraic subgroup product.

## Proved elementary consequences

The following are proved laws, rather than extra fields of the definition:

- `IsPseudoParabolicSubgroup.isClosedSubgroup` extracts closedness from the
  represented product in the presentation.
- `IsPseudoParabolicSubgroup.exists_cocharacter_product` allows any supplied
  representative `j` satisfying `IsUnipotentRadical j` to serve as the
  radical factor. The proof takes a presentation, uses
  `IsUnipotentRadical.range_eq` to identify its radical's all-test image with
  that of `j`, and rewrites the same product predicate. It retains the
  presentation's cocharacter.
- `IsPseudoParabolicSubgroup.radical_le` applies the preceding law and the
  represented product's `right_le` law. It gives containment of every supplied
  represented ground-field radical on all tests.
- `IsPseudoParabolicSubgroup.exists_cocharacter_le` takes the presentation's
  cocharacter and applies the product's `left_le` law.

Smoothness and connectedness of `P` are not fields or proved consequences
here. Radical existence for arbitrary `G`, quotient construction and geometry,
pseudo-completeness, and rational conjugacy remain separate structure
theorems. CGP's warning immediately after Definition 2.2.1 says that `G/P`
need not be proper over imperfect fields, even for pseudo-reductive `G`;
no quotient-properness claim is made here.
