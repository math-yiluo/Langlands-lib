# Proof: discreteness of rational and integral affine points in adelic points

Proof author: Worker 105. Current-Library verification and submission: Worker 1584.

This module proves `Langlands.Global.AdelicRationalPointsDiscreteStatement`
(`AdelicRationalPointsDiscreteStatement.lean`), the formalization of the last sentence
of Conrad's Example 2.2 and the first two sentences of Example 2.3 (Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011, printed p.3).
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The final theorem is `Langlands.Global.adelicRationalPointsDiscrete_proof`,
in an arbitrary universe `u`. The target and its import closure are unchanged.

## Generic transfer

`isEmbedding_of_injective_of_discreteTopology_range`: an injective map `f : X → Y` from
a discrete space whose image is discrete in the subspace topology is an embedding. The
bijection `Equiv.ofInjective f` from `X` to `Set.range f` is continuous in both directions
because both sides are discrete, so it is a homeomorphism; composing with the subtype
inclusion recovers `f`.

`affineDiscreteSubringProperty_proof R T` proves `AffineDiscreteSubringProperty R T`.
Give `R` the discrete topology `⊥`. The previous lemma makes the structure map
`Algebra.ofId R T` an embedding. The published coefficient-change result
`affineSchemeCoefficientEmbeddings_proof` then makes the induced map on actual points
`RingPoint.changeRing (Algebra.ofId R T)` an embedding, for every affine `X` over
`Spec R`. This transfer needs only the given topology on `T`, without
assuming that its ring operations are continuous. For `X` locally of finite type, `affineSchemeDiscrete_proof R R` shows the
source `RingPoint R X R` is discrete. An embedding is a homeomorphism onto its image
(`IsEmbedding.toHomeomorph`), so the image is discrete too.

## Discrete image from an isolating neighbourhood

`discreteTopology_range_of_isolating`: let `f : A →+* B` be a ring map into a topological
ring and `U` an open set containing `0` such that `f a ∈ U` forces `f a = 0`. Then the
image of `f` is discrete. The proof applies `discreteTopology_of_isOpen_singleton_zero`
to the subring `f.range`: the trace of `U` on `f.range` is exactly `{0}`. The set
`Set.range f` is the carrier of `f.range` (`RingHom.coe_range`).

## The four arithmetic cases

Each case applies the generic transfer. It checks injectivity of the structure map and
gives an isolating neighbourhood, using existing Library arithmetic.

- **Number field, rational points** (`numberFieldRationalPointsDiscrete_proof`).
  Injectivity is Mathlib's `NumberField.AdeleRing.algebraMap_injective`. The isolating
  set is `principalAdelesIsolatingSet K`: archimedean norms `< 1` and integral finite
  components. It is open and contains `0`, and
  `principalAdelesIsolatingSet_inter_principalAdeles` shows it meets the principal
  adeles only in `0`.
- **Number field, `S`-integral points** (`numberFieldIntegralPointsDiscrete_proof`).
  The structure map of `(S : Set (FinitePlace K)).integer K` into
  `numberFieldAdeleLevel K S` is `numberFieldAdeleLevelDiagonal`. Its value in `Adeles K`
  is by definition the diagonal image of the underlying field element. Injectivity
  therefore follows from the full diagonal. The isolating set is the preimage of
  `principalAdelesIsolatingSet K` under the subtype inclusion, which is open in the level
  subspace topology.
- **Function field, rational points** (`curvePlaceRationalPointsDiscrete_proof`).
  Injectivity: evaluate at the actual place `curvePlaceReference k F`, where the map is
  the field embedding into a completion. The isolating set is
  `curvePlaceDiagonalIsolatingSet k F`: integral at every actual place and of valuation
  `< 1` at `curvePlaceReference k F`. `curvePlaceDiagonalIsolatingSet_inter_range`
  shows the diagonal meets it only in `0`. This lemma uses the statement's
  `PerfectField k` hypothesis.
- **Function field, outside-`S` integral points**
  (`curvePlaceIntegralPointsDiscrete_proof`). This case has no perfectness hypothesis.
  The structure map is `curvePlaceAdeleLevelDiagonal`, whose coordinate at `v` is the
  completion map applied to the underlying field element. Injectivity again comes from
  evaluation at `curvePlaceReference k F`. The isolating set is the preimage of
  `curvePlaceDiagonalIsolatingSet k F` in the level. Its openness and zero membership
  do not use perfectness. If an outside-`S` integer `c` lands in it, then `c` is
  integral at every actual place (`curvePlaceCompletion_mem_integers_iff`) and has
  valuation `< 1` at the reference place. The Library lemma
  `eq_zero_of_forall_mem_curvePlace_of_lt_one`, which also does not assume perfectness,
  then forces `c = 0`.
