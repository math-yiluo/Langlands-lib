# Finite length and exactness of the actual product-Levi refinement functors

Author: Worker 717.

`Langlands.Parabolic.normalizedRefinedFiniteLengthExactness.{uF,uV} F T`
proves exactly the published proposition
`Langlands.Parabolic.NormalizedRefinedFiniteLengthExactnessStatement.{uF,uV} F T`
of `Langlands.Representation.Parabolic.RefinedFiniteLengthFunctorStatement`.
Its outer binders are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with independent field and input-carrier universes
`uF` and `uV`. There are no other premises. The statement pair and the
definitions it uses are imported unchanged.

The proposition is the ordered, right-associated conjunction of four clauses.
Each clause quantifies every natural rank `n`, every ordered outer block shape
`B : BlockShape n` and every block refinement `S : BlockRefinement B`.

1. `NormalizedRefinedInductionFiniteLengthStatement`: the actual normalized
   refined induction functor `T.normalizedRefinedInductionFunctor B S` sends
   smooth refined-Levi representations of finite group-algebra length, with
   carrier in `Type uV`, to product-Levi representations of finite length,
   with carrier in `Type (max uF uV)`.
2. `NormalizedRefinedJacquetFiniteLengthStatement`: the actual normalized
   refined Jacquet functor `T.normalizedRefinedJacquetFunctor B S` does the
   same from the product Levi `B.Levi F.Carrier` to the refined Levi. The
   carrier universe stays `uV`.
3. `NormalizedRefinedInductionShortExactStatement`: refined induction sends
   every short exact sequence of finite-length smooth objects to a short exact
   sequence. Here "short exact" means `SmoothRep.IsShortExact`: the first
   intertwiner is injective, the second is surjective, and range equals kernel.
4. `NormalizedRefinedJacquetShortExactStatement`: the same for the refined
   Jacquet functor.

The closing theorem pairs the four helper theorems of the namespace
`Langlands.Parabolic.RefinedFiniteLengthFunctorAssembly`, described below.
Every input is an arbitrary smooth representation of finite length. None of the
helpers assumes admissibility, finite generation, irreducibility, cuspidality,
a tensor decomposition, a central character, finite dimension or positive rank.

## Conventions retained

The functors are the published ones in `Geometric.RefinementFunctors`, used
with the supplied `T.topology`. Normalized refined induction is smooth induction
from the actual refined parabolic `refinedParabolic F.Carrier B S` to the actual
product Levi. The inducing representation is inflated through the actual
projection `refinedLeviProjection` and twisted by the positive half-modulus
`T.refinedParabolicHalfModulus B S`. The product Levi acts by right
translation. The functor maps a morphism to postcomposition by its
inflated and twisted intertwiner. The refined Jacquet functor takes
coinvariants of the actual refined unipotent subgroup, with the inverse
half-modulus action `T.refinedLeviInverseHalfModulus B S`, and maps a
morphism to the induced map of coinvariants. The proof uses these maps
directly, through their definitional unfolding. It defines no substitute
functor and changes no normalization.

The standard functors used in the finite-length arguments are the published
`T.normalizedParabolicInduced` of `Induction.Parabolic` and
`T.normalizedJacquet` of `Jacquet.Parabolic`. Induction there is from the upper block
parabolic of `GL_n`, with positive half-modulus. Jacquet uses the upper block
unipotent coinvariants, twisted by the inverse half-modulus.

## All-rank handling

No step splits on the rank, the number of blocks or the size of the input.
Every lower theorem used below is stated and proved for all ranks, shapes and
refinements, including rank zero and empty products. Zero representations are
covered as ordinary finite-length inputs. The finite-length conjuncts apply the
all-rank published theorem
`Langlands.Parabolic.normalizedParabolicFiniteLength`. That theorem handles
rank zero separately inside its own proof; this module needs no case split.

## Finite length of refined induction

`normalizedParabolicInduced_refinedInduced_finiteLength` proves the following.
Let `A` be a smooth refined-Levi representation `σ` of finite length. Then the
standard normalized induction to `GL_n` of its normalized refined induction,
`T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S σ)`, has finite
length over `ℂ[GL_n(F)]`. The proof has three steps.

- **Coordinate transport.** `e := Geometric.flattenedLeviEquiv F.Carrier B S`
  is the constructed group isomorphism from the standard Levi of the flattened
  shape `B.flatten S` onto the actual refined Levi. The pullback `σ ∘ e` is
  smooth because `flattenedLeviEquivContinuous` makes `e` a homeomorphism.
  `FiniteLengthAssembly.finiteLength_comp_surjective_iff` gives finite length
  of `σ ∘ e` over the flattened Levi group algebra, since `e` is surjective.
- **Standard length.** The induction conjunct of
  `normalizedParabolicFiniteLength.{uF,uV}` at the flattened shape gives
  finite length of `T.normalizedParabolicInduced (B.flatten S) (σ ∘ e)`.
- **Induction in stages.** The published
  `normalizedRefinementInductionTransitivity` provides a natural isomorphism
  between outer induction composed with refined induction and the actual direct
  composed induction `T.normalizedComposedInductionFunctor B S`. Its component
  at `A`, unfolded to an equivalence of representations, is `E₁`. The published
  `composedFlattenedInduction` provides an equivalence `E₂` from composed
  induction to standard flattened induction of `σ ∘ e`. The composite `E₂ ∘ E₁`
  is an injective intertwiner into a finite-length representation. So
  `FiniteLengthAssembly.finiteLength_of_injective` gives finite length of the
  iterated induction.

`inductionFiniteLength` then proves the first clause. Write `ρI` for the actual
refined induced representation and `J` for its standard normalized induction.
`T.isSmooth_normalizedRefinedInduced` and
`T.isSmooth_normalizedParabolicInduced` give smoothness of `ρI` and `J`. The
Jacquet conjunct of `normalizedParabolicFiniteLength.{uF, max uF uV}` gives
finite length of `T.normalizedJacquet B J` over the product-Levi group algebra.
This instance is used because `J` has carrier universe `max uF uV`.

The published `CuspidalSupport.jacquetEvaluation T B (id J)` is evaluation at the
identity, descended to the normalized Jacquet module. It is an intertwiner from
`T.normalizedJacquet B J` onto `ρI`. The inverse half-modulus of the Jacquet
action cancels the positive half-modulus of induction. The published
`CuspidalSupport.jacquetEvaluation_id_surjective` proves that this map is
surjective for smooth `ρI`, using compactly supported local sections.
`FiniteLengthAssembly.finiteLength_of_surjective` then transfers finite length
to `ρI`.

## Finite length of refined Jacquet

`normalizedRefinedJacquetMap_surjective` proves that the actual refined Jacquet
map of a surjective intertwiner is surjective. By the published `rfl` lemma
`CuspidalSupport.RefinedJacquetLengthProof.map_toLinearMap`, its underlying
linear map is the coinvariant map of the original intertwiner. The
normalization changes only the action. `Langlands.coinvariants_map_surjective`
finishes the proof.

`jacquetFiniteLength` proves the second clause. Let `σ` be a smooth
product-Levi representation of finite length, and let `X` be its standard
normalized induction to `GL_n`. The induction conjunct of
`normalizedParabolicFiniteLength` gives finite length of `X`. The Jacquet
conjunct, at carrier universe `max uF uV`, then gives finite length of the
standard normalized Jacquet module of `X` at the flattened shape `B.flatten S`.

The published `flattenedJacquetQuotient` supplies a surjective intertwiner. It
maps that flattened Jacquet module onto the iterated normalized Jacquet module
`T.normalizedRefinedJacquet B S (T.normalizedJacquet B X)`, pulled back along
`e = flattenedLeviEquiv`. Its underlying map is the actual flattening quotient.
So the pullback has finite length. Since `e` is surjective,
`finiteLength_comp_surjective_iff` gives finite length over the refined Levi
group algebra itself.

Finally, `jacquetEvaluation T B (id X)` maps `T.normalizedJacquet B X` onto `σ`
and is surjective because `σ` is smooth. Its refined Jacquet map is therefore
surjective onto `T.normalizedRefinedJacquet B S σ`. This makes the target a
quotient of a finite-length representation.

## Exactness of refined induction

`inductionShortExact` proves the third clause. Let `f : A ⟶ D` and
`g : D ⟶ E` form a short exact sequence. The functor's map on a morphism is
definitionally `Induction.smoothInducedMap` applied to the inflated, twisted
intertwiner. That intertwiner has the same underlying linear map. To match the
functor's instances, the proof installs the product-Levi topological group
structure built from `T.valuativeRel` and `T.localField`.

- Injectivity of the induced first map is
  `Induction.smoothInducedMap_injective`, since postcomposition by an
  injective map is injective on functions.
- Range equals kernel by `Induction.smoothInducedMap_range_eq_ker` from
  `Parabolic.InductionExactnessProof`. A function killed by the second map
  lifts pointwise and uniquely through the injective first map, and the lift
  keeps the right stabilizer.
- Surjectivity of the induced second map is
  `normalizedRefinedInducedMap_surjective`. It applies the published
  `Induction.smoothInductionSurjectivity` to the product Levi and the closed
  subgroup `refinedParabolic F.Carrier B S`. Closedness is
  `isClosed_refinedParabolic`: the refined parabolic is the product of the
  closed block parabolics, under the Hausdorff field topology `T.fieldT2`. The
  compact-open basis comes from `T.leviCompactOpen B`. The twisted inflations
  of `D` and `E` are smooth because `refinedLeviProjectionContinuous` is
  continuous and the half-modulus has open kernel. This uses only the
  smoothness of `D` and `E`.

The two surjectivity lemmas `isClosed_refinedParabolic` and
`normalizedRefinedInducedMap_surjective` are restated and re-proved verbatim in
this namespace. The originals are the identically named lemmas of the published
`Classification.NestedInductionProof` (Worker 379). Importing that module would
add it and `Classification.NestedInductionStatement`, which this proof does not
otherwise need, to the import closure. Its remaining imports are in the closure
already.

The finite-length hypotheses on `A`, `D` and `E` are part of the predicate but
are not needed for exactness.

## Exactness of refined Jacquet

`jacquetShortExact` proves the fourth clause. It applies the published
`CuspidalSupport.RefinedJacquetLengthProof.map_exact` to the actual
intertwiners. That theorem needs only smoothness of the middle object `D`, and
returns injectivity, range equals kernel, and surjectivity of the actual
refined Jacquet maps. The proof reorders these into the order of
`SmoothRep.IsShortExact`. The functor's map on morphisms is definitionally
`T.normalizedRefinedJacquetMap B S`.

## Universes

Induction takes input carriers in `uV` to outputs in `max uF uV`. Jacquet keeps
`uV`. The standard theorem is used at `uV` for the first induction and at
`max uF uV` for the Jacquet step applied to induced objects. No resizing is
used. Inspection of the closing theorem reports universe parameters `[uF, uV]`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Independence of the lower inputs

The direct project imports are the target
`Parabolic.RefinedFiniteLengthFunctorStatement`,
`Parabolic.FiniteLengthFunctorProof`,
`CuspidalSupport.RefinedCuspidalInductionReduction`,
`CuspidalSupport.RefinedJacquetLengthProof`,
`Parabolic.FlattenedJacquetQuotientProof` and
`Parabolic.InductionExactnessProof`, all under `Langlands.Representation`.
Induction in stages (`Parabolic.RefinementInductionTransitivityProof`), the
composed–flattened comparison (`Parabolic.ComposedFlattenedInductionProof`),
smooth-induction surjectivity (`Induction.SurjectivityProof`) and the
finite-length transport lemmas (`Classification.FiniteLengthProof`) enter
through these imports.

The audit used Library commit `b22e185743f7c318f709e14e422801f4360105d5`.
The transitive project import closure has 603 modules, all with nonempty
paired Markdown. None of the excluded tasks' proof modules exists in this
Library:

- analytic segment classification;
- special-head multisegment exhaustion;
- ordered strong-head existence;
- quotient coverage;
- tempered block uniqueness;
- square-integrable Langlands classification;
- square-integrable exhaustion;
- regular exhaustion.

Their would-be names are
`Classification.{SegmentEssentialSquareIntegrableClassification,
MultisegmentHeadExhaustion, OrderedMultisegmentHeadExistence,
OrderedMultisegmentQuotientExhaustion, TemperedBlockUniqueness,
SquareIntegrableLanglandsClassification, SquareIntegrableLanglandsExhaustion,
RegularLanglandsExhaustion}Proof`. A case-insensitive scan of every Lean source
in the closure found none of their statement or proof names. So no excluded
conclusion, proof successor or transitive proof dependency is used.

The only deep lower input is the standard all-rank theorem
`normalizedParabolicFiniteLength`. Its own Markdown documents its route and
independence audit:

- admissibility of finite-length representations;
- finite length of induction of admissible finite-length Levi inputs, through
  Levi factorization, irreducible products and cuspidal-induction length;
- Jacquet length through the quasicuspidal decomposition and refined Jacquet
  induction.

The other inputs are explicit constructions on the actual function and
coinvariant spaces: transitivity, flattening, evaluation and exactness. Their
paired Markdown describes them.

## Source correspondence

The four clauses are the product-Levi case of standard exactness and
transitivity properties. In Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977):

- Proposition 1.9(a), printed p.445, gives exactness of the normalized
  induction functors and, for a unipotent group that is a limit of compact
  subgroups, of the normalized Jacquet functor.
- Proposition 1.9(c) gives induction and Jacquet functors in stages.
- Section 2.2, printed p.446, identifies the standard subgroups of `GL(n)`
  with ordered partitions, a subpartition giving a standard subgroup inside a
  product Levi.
- Proposition 2.3(a),(c), printed p.446, restates exactness and transitivity
  for standard subgroups `N < M < G`.

Here `M` is the product Levi `B.Levi F.Carrier`, a product of general linear
groups, and `N` is the refined Levi. The Lean exactness proofs apply these
facts to the actual product Levi directly. Neither proof factors through
`GL_n`.

In Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups* (draft of 1 May 1995):

- Proposition 2.4.4, printed p.28, states that smooth induction from a closed
  subgroup maps a morphism to a surjection, or an injection, exactly when the
  morphism is one, and that induction is exact.
- Proposition 3.2.3, printed p.34, gives exactness of unipotent coinvariants.
- Theorem 3.2.4, printed p.34, is Frobenius reciprocity through evaluation at
  the identity, which underlies the Jacquet evaluation map.
- Section 3.1, printed p.32, fixes normalized induction.

The original passages were read directly at these pages. The finite-length
clauses are not proved in these sources for arbitrary smooth finite-length
inputs within a product Levi. Here they are derived: the published standard
theorem is transported through the flattened Levi equivalence, induction in
stages and the flattened Jacquet quotient, as above. This derived route is
internal to the project. The published statement Markdown explains the
admissibility bridge for the source scope.

Registered sources:

- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. One-based
  PDF page equals printed page minus 439.
- `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`. Printed
  and PDF pages agree.

No errata note for either source was present in the public notes.
