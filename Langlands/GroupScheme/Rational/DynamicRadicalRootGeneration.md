# Dynamic radical containment from disjoint positive root rays

This internal module works at one connected reductive group over an arbitrary
field `k : Type u`, one actual maximal split torus `i : S → G`, and one
cocharacter `ν`. It assumes that the positive integral rays of distinct
indivisible positive actual roots are disjoint. No global relative-root-system
statement, root-ray statement, or ordered-root-product statement is assumed.

`dynamicUnipotent_le_of_disjoint_positive_rays` proves that every subgroup `K`
of `G(k)` containing all actual relative root-group points contains the complete
dynamic radical `U(ν)(k)`. `dynamicRadicalRootInclusion` packages this inequality
as the identity inclusion homomorphism. Its coercion lemma records that the
underlying rational point is unchanged.

The proof specializes the construction in `DynamicRootProductAssembly` to
this single group, torus, and cocharacter. All its structural ingredients
other than the displayed local disjointness premise are proved Library results:

- `semigroupRealization` represents the positive-weight semigroup subgroup
  by a smooth connected affine unipotent group `U`.
- The induced torus action on `U` has weight support exactly the positive
  actual roots.
- Finiteness gives an injective enumeration of the indivisible positive roots.
  `positive_iff_mem_indivisiblePositiveRoot_ray` gives coverage without a
  root-system assumption. The local disjointness premise supplies the
  cross-exclusion needed by the ordered semigroup product theorem.
- `hasOrderedSemigroupProducts_of_unipotent` gives an isomorphism from the
  finite ordered product of the resulting represented factors onto `U`.
- `cyclicRootFunctorComparison` identifies each ambient factor with the full
  actual root subgroup, retaining doubled-root points inside that factor.
  `dynamicSemigroupComparison` identifies `U` with the actual dynamic radical.

A rational radical point lifts to `U` and then through the product isomorphism.
Evaluation of ordered multiplication is a finite list product of rational
points in the actual root groups. Each factor lies in `K`, so their product
does too. This includes an empty positive-root set and any cocharacter,
including zero or nongeneric cocharacters.

The provenance is internal: this is a local consumer of already proved
semigroup realization, transport, product, and comparison results, derived
from the published assembly's construction. It proves neither the local
ray-disjointness premise nor the global `DynamicRootOrderedProductStatement`.
