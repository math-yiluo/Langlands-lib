# The finite induced-cuspidal embedding from the whole-category splitting

Worker 4957. This module reduces the finite induced-cuspidal embedding of
Renard VI.7.2,
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalInducedEmbeddingStatement.{u,v}`,
to one published proposition that is not yet proved: the first decomposition
of Renard VI.3.5,
`Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u,v}`.
It therefore does not prove the embedding statement. It is an internal step of
proof task `198824c2-4e2f-40c1-94a0-07fa748bede9`. No source states this
implication as a separate result.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In VI.7.2,
printed pp.182–183 / PDF pp.188–189, the functor `R` takes the cuspidal part
of each standard Jacquet module. That cuspidal part exists by the splitting of
VI.3.5, printed pp.146–147 / PDF pp.152–153, applied to the Levi subgroup. The
reduction below makes this dependence exact: the VI.3.5 statement is the only
input still needed.

## Declarations

- `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`: the VI.3.5
  whole-category statement at universes `u, v` implies the published
  `RationalLeviJacquetCuspidalRemainderSplittingStatement.{u,v}` of
  `RationalFiniteCuspidalEmbeddingReduction`.
- `rationalCuspidalInducedEmbedding_of_wholeStatement`: the VI.3.5
  whole-category statement at universes `u, v` implies
  `RationalCuspidalInducedEmbeddingStatement.{u,v}`.
- `rationalCuspidalInducedEmbeddingOfWholeStatement`: the second theorem as a
  `def` whose type is the implication between the two published propositions.

The field and group universe `u` and the representation carrier universe `v`
stay independent. Both propositions are used exactly as published; this module
changes neither.

## The proof

The first theorem introduces the data of the splitting statement exactly as
that statement binds them. These are the field `k`, the connected reductive
group scheme `G`, the maximal split torus `i : T.toGrp ⟶ G`, the canonical
point topology on `RationalPoint k G.X` and its three topology instances, a
generic cocharacter `ν`, and `hStandard`, `hInter`, `hRoots`, `hU` and `hM`.
It also fixes the simple-root enumeration
`simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν`. For a smooth
representation `A` with carrier in `Type v` and a standard index `I`, it
proves the splitting of the actual normalized Jacquet module
`(jacquetFunctor h_I (hU I)).obj A`, where
`h_I = isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I`.

1. The represented standard Levi `Standard.leviScheme i ν (rootSet i ν I)` is
   connected reductive by the published
   `standardLeviScheme_isConnectedReductive`. Its centralizer premise is
   discharged by the published unconditional `dynamicCentralizerReductive`
   (Workers 1325 and 1326).
2. The intrinsic maximal split torus of that Levi has a relative root system
   by the published `HasRelativeRootSystem.of_standardLeviTorusFactor`. It is
   applied to the ambient `hRoots`, `hStandard`, `hG`, `hi`, `ν`, `hν`, the
   root set `rootSet i ν I` with `rootSet_subset i ν I`, the reductivity of
   step 1, the Levi morphism `Standard.leviHom` and its published
   representation and closedness facts `Standard.isRepresentedBy_leviHom` and
   `Standard.isClosedSubgroup_leviHom`.
3. Worker 1570's published `hasLeviCuspidalRemainderSplitting_of_wholeStatement`
   takes the whole-category statement, the ambient data, `hU`, the closedness
   `hM I` of the literal Levi and the root system of step 2. It gives
   `HasLeviCuspidalRemainderSplitting` for every smooth representation of the
   literal Levi subgroup with carrier in `Type v`. It is applied to the
   Jacquet module above, whose carrier is again in `Type v`.

The second theorem applies Worker 1570's published
`rationalCuspidalInducedEmbedding_of_leviJacquetSplittings` to the first.

## How the embedding is built

The published reduction of the second step builds the embedding from the
splittings as follows. Here it is
`finiteCuspidalInducedEmbedding_of_splittings` and
`finiteCuspidalInducedEmbedding_of_projections`, from
`CuspidalJacquetProjectionFromSplitting` and `FiniteCuspidalEmbeddingAssembly`.

- Each splitting gives a cuspidal object `τ I` of the literal Levi `M I`, with
  carrier in `Type (max u v)`. It also gives an equivariant map from the
  Jacquet module of the source to `τ I`. Composing with this map kills no
  nonzero map from a cuspidal object.
- Frobenius reciprocity turns these maps into maps from the source to the
  actual normalized inductions `(normalizedInductionFunctor h_I (hU I)).obj (τ I)`.
  Their sum over the finite index `Finset (SimpleRoot i ν)` is the map into the
  actual `SmoothRep.directSum`. Unimodularity and compact-limit regularity of
  the standard unipotent radicals come from the published rational regularity
  theorems.
- Let `K` be the kernel of this map. If `K` were nonzero, Worker 1784's
  published `exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier` would
  give an index `I` whose Jacquet module of `K` is nonzero and cuspidal. That
  module maps injectively into the Jacquet module of the source, and the
  projection kills this map. The projection property then forces the map to
  be zero, a contradiction. So the map is injective.

The source instead proves that the adjunction unit of the faithful exact left
adjoint `R` is injective. The implemented route uses the same component maps
but argues directly on their kernel. No exactness of induction and no
faithfulness of `I` or `R` is used.

## Scope

The only hypothesis is the VI.3.5 whole-category statement. Its proof is task
`4bee987a-093b-4054-bd65-7360168351d2`. No admissibility, finite length, finite
generation, cuspidal decomposition of the source or faithful I/R unit is added
to the embedding statement. Once VI.3.5 is proved, the embedding statement is
the direct application `rationalCuspidalInducedEmbedding_of_wholeStatement hwhole`.
