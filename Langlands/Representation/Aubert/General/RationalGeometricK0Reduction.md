# The rational geometric-lemma K0 expansion from parabolic points and epsilon balance

Module: `Langlands.Representation.Aubert.General.RationalGeometricK0Reduction`,
namespace `Langlands.Aubert.General.RationalPointFamily`. Author: Worker 4021.

This module proves the conclusion of the published target
`RationalGeometricK0ExpansionStatement` (module `RationalGeometricK0Target`),
conditional on two named inputs. It does not prove the target itself: the
conditional theorem keeps both inputs as explicit premises.

## Conditional theorem

`geometricK0Expansion_of_points_of_balance` works over a nonarchimedean local
field `k`, with `G(k)` given the canonical `pointTopology`. Its section
variables are exactly the target's displayed data and premises:

- `IsAffineHom`, local compactness, the nonarchimedean group structure and
  Hausdorffness of `G(k)`;
- the maximal split torus `i`, the generic cocharacter `ν` and
  `StandardCocharacterStatement`;
- closedness of the standard unipotent, parabolic and Levi subgroups
  (`hU`, `hP`, `hM`);
- continuity of the derived standard Levi projections (`hproj`);
- the limit-of-compact-subgroups property of each `U_I` (`hUc`);
- finite-length preservation of ambient normalized induction and Jacquet
  restriction (`hiFl`, `hrFl`);
- finiteness of the relative Weyl group;
- `HasPointNormalizerComparison` and `HasPointCentralizerComparison`;
- the actual Coxeter system `cs` and `actualLeviWeylIdentification`;
- the target's `GeometricIntersectionDecompositions` (`hGeom`) and
  `GeometricTermFiniteLength` (`hTermFl`) premises.

It assumes two further inputs:

1. `hPoints : StandardParabolicPointsStatement.{u}`, the published Bruhat /
   parabolic-double-coset statement (proof task: Task 3790).
2. `hε`: for all `I`, `J` and all actual torus-normalizer points `n`,
   `geometricEpsilonOne … n * geometricEpsilonTwo … n = 1`. This is the
   cancellation of the two original Haar corrections, for the decompositions
   `isSemidirectDecomposition_of_standardCocharacterStatement`.

Its conclusion is literally the target's body:

`GeometricK0ExpansionStatement (parabolic i ν) (levi i ν) (unipotent i ν) (isSemidirectDecomposition_of_standardCocharacterStatement …) hU (standardParabolicFiniteLength …) hM (torusPoints i) cs hGeom hTermFl`.

So for every `I`, `J`, every section `lift` of the actual normalizer quotient
and every finite-length class,

`r_I ∘ i_J = ∑_{w ∈ minimalReps cs I J} geometricTermK0 I J (lift w)`

holds as actual `ℤ`-linear maps on exact `K0`. Each summand uses the original
`hGeom` decompositions and `hTermFl` finite-length witnesses at `lift w`.

`geometricK0ExpansionOfPointsOfBalance` is the same result packaged as a
declaration whose type is the implication
`StandardParabolicPointsStatement → (∀ I J n, ε₁ε₂ = 1) → GeometricK0ExpansionStatement …`,
with the same section variables. Its body applies the theorem.

## Proof

1. **Ordering.** `minimalOrbitOrdering` (module
   `RationalGeometricOrbitOrdering`, using `hPoints`) provides an equivalence
   `e : Fin m ≃ minimalReps cs I J` and an ordered orbit cover `t` of
   `P_J \ G(k)` by `P_I`-orbits with `t.representative q = lift (e q)`.
   Second countability, and hence σ-compactness, of `G(k)` comes from the
   published `reductiveRationalPoint_secondCountable`.
2. **Graded pieces.** The support filtration
   `jacquetSupportFiltration (dec J) (hU J) (dec I) (hU I) t` (module
   `ParabolicSupportFiltration`) filters `r_I ∘ i_J`. For each `q`,
   `jacquetSupportGeometricTermIso` (module `RationalGeometricOrbitTerm`,
   using `hε` at `lift (e q)`) identifies the `q`-th grade with
   `geometricTermFunctor … I J (lift (e q)) hs ht ⋙ SmoothRep.toRep`, where
   `hs` and `ht` are the target's own `hGeom` components.
   `isGluedFrom_of_hasGradedPieces` packages this as `IsGluedFrom`, and
   `Functor.assoc` rebrackets the composite functor.
3. **Exact K0.** The published `SmoothRep.filtrationGrothendieckStatement`
   turns the gluing into an equation of finite-length classes. On a
   finite-length object `X` of `M_J`, the class of `r_I(i_J X)` is the sum of
   the classes of the pieces.
4. **Identification of both sides.** By
   `FiniteLengthGrothendieckGroup.hom_ext_object` it suffices to compare
   values on objects. The left side reduces by `inductionK0_ofRepresentation`
   and `jacquetK0_ofRepresentation`. On the right, `LinearMap.sum_apply` and
   `geometricTermK0_ofRepresentation` reduce each summand to the class of the
   geometric term. Reindexing along `e` (`Fintype.sum_equiv`) matches the two
   sums.

The convention `P_J w⁻¹` in `P_J \ G / P_I` versus the target's
`W_I \ W / W_J` is handled in `RationalGeometricOrbitOrdering`. Both Haar
corrections, the positive and inverse half-moduli, the compact/smooth
induction comparison and the smooth realization are handled in
`RationalGeometricOrbitTerm` and `RationalGeometricOrbitSource`.

## Provenance and dependencies

This is the geometric lemma, BZ77 2.12/5.2 and Renard VI.5.1, in exact K0 form,
assembled from the declarations named above. Proof-body dependencies are:

- the published support filtration;
- the orbit-term comparison, which in turn uses the published normalized
  compact comparison, `compactSmoothIso`, `dynamicParabolicQuotientCompact`
  and the common-Levi refinements;
- the ordering, which uses `closedSubgroupOrbitOrdering` and the published
  parabolic double-coset comparison;
- the published K0 filtration additivity.

These proof bodies themselves invoke no adjointness, cuspidal support,
character independence or Langlands classification. The imported
module closure is larger. The two inputs `hPoints` and `hε` remain open
obligations.
