# Almost-all exact integral and native level lifts across target components

`Langlands.Global.adelicLevelComponentSurjectivity.{u}` proves
`Langlands.Global.AdelicLevelComponentSurjectivityStatement.{u}`. Both clauses
of the target are implications from `UniformLangWeilStatement.{u}`. The proof
keeps that estimate as an explicit premise and does not prove it. It also
keeps every other stated hypothesis: the target model's structure map to the
lifted integer spectrum is locally of finite type, its underlying space is
compact, and the morphism is smooth, separated, quasi-compact and
geometrically connected. No common fibre dimension is supplied or used. The
fields, schemes and native rings live in one arbitrary universe `u`.

## Source

This is step (ii) of the proof of Conrad's Theorem 4.5 in
`conrad-2011-weil-grothendieck-adelic-points` (printed pp.12–13). Step (ii)
says that for all but finitely many places `v ∉ S`, the map
`X'_{S,v}(O_v) → X_{S,v}(O_v)` is surjective. Conrad reduces this to
surjectivity on residue-field points, using Hensel lifting over the henselian
ring `O_v` [EGA IV4, 18.5.17]. He passes to the connected components of the
target to get a common fibre dimension `d`. Lemma 4.6 then gives a rational
point in every fibre over a residue field of large enough size.

The Lean statement makes a requirement at every enlarged level `T ⊇ S` and
at every native factor of that level. Only cofinitely many factors must give
surjective maps. The proof takes the finitely many completed-field factors
(and, for number fields, the infinite factors) as exceptions. It makes no
surjectivity claim about them.

## Route

The proof does not repeat the component decomposition or the Hensel lifting.
Both come from the published constructor
`Langlands.AlgebraicGeometry.PointTopology.uniformLangWeilComponentHenselianRingPointLifts`
in module `Langlands.AlgebraicGeometry.UniformLangWeilComponentLiftingProof`.
Given uniform Lang–Weil and the stated hypotheses on the actual relative
morphism `f : Y ⟶ B` over `Spec C`, it returns a constant `C > 0`. For any
Henselian local `C`-algebra `R` and any surjective `C`-algebra map from `R`
to a finite field `K` with `C^2 < #K`, it also lifts every `RingPoint C B R`
exactly to a `RingPoint C Y R` over it. The constructor handles the finitely
many target components and their differing dimensions itself.

### Integral constructors

The constructors `curvePlaceComponentAlmostAllIntegralPointLifts` (global
function fields with finite constant field) and
`numberFieldComponentAlmostAllIntegralPointLifts` (finite places of number
fields) take any coefficient ring `C`. They apply the constructor above to
`f`, with constant `c`. The exceptional set is exactly the finite set of
places whose completed residue field has cardinality at most `c^2`:

- `curvePlaceSmallCompletionResiduePlaces k F (c ^ 2)`, or
- `finitePlaceSmallCompletionResiduePlaces K (c ^ 2)`,

both from module `Langlands.Global.CompletionResidueBounds`. Take a place
outside this set:

- The native completion integer ring is Henselian, by
  `curvePlaceCompletionIntegers_henselian` or
  `adicCompletionIntegers_henselian`.
- Its residue field is finite. In the function-field case the proof
  supplies `curvePlaceCompletionResidue_finite` explicitly. In the
  number-field case instance inference finds it, for example through
  `Langlands.Global.CompletionResidue.finite_adicResidueField`.
- Its residue cardinality exceeds `c^2`, by the `_lt` lemma of the
  exceptional set.

The proof applies the constructor to the canonical residue map
`IsScalarTower.toAlgHom C O (ResidueField O)`, which is surjective by
`IsLocalRing.residue_surjective`. The `C`-algebra structure on the completion
integer ring is an argument at each place, so the caller supplies the
original coefficient action.

### Level constructors

Let `T` be an enlarged level. In the function-field case,
`curvePlaceLevelComponentPointLifts` declares these indices exceptional:

- every completed-field index `Sum.inl v`, for `v ∈ T`;
- every integral index `Sum.inr v` whose place `v.1` lies in the
  small-residue set.

In the number-field case, `numberFieldLevelComponentPointLifts` declares
these indices exceptional:

- every infinite index `Sum.inl w`;
- every finite completed-field index `Sum.inr (Sum.inl v)`, for `v ∈ T`;
- every integral index `Sum.inr (Sum.inr v)` whose place lies in the
  small-residue set.

The index types `{v // v ∈ T}` and `InfinitePlace K` are finite. The integral
exceptions are the preimage of a finite set under the injective subtype
projection, so they are finite too. Every other index is a completed integer
ring `curvePlaceCompletionIntegers v.1` or `v.1.adicCompletionIntegers K` at
a place outside the small-residue set. The level-factor algebra
over the original fixed base, `curvePlaceSIntegers k F S` or
`(S : Set (FinitePlace K)).integer K`, is transported by `inferInstanceAs`.
It is passed to the integral constructor, so each lift is a `RingPoint` over
the original base. The proof uses the original level-factor types and their
coefficient actions without change.

### Endpoint

`curvePlaceLevel_component_eventually_surjective` and
`numberFieldLevel_component_eventually_surjective` use
`Finset.eventually_cofinite_notMem`. Outside the finite exceptional set, the
constructed lift shows that `p ↦ p ≫ f` is surjective. The theorem
`adelicLevelComponentSurjectivity` puts the two clauses together.

## Scope

This proof does not supply the uniform Lang–Weil estimate (Lemma 4.6),
compatible smooth models, absolute arithmetic finite type, local openness or
adelic openness. Those stay with the parent task
`886bf565-95e9-4dc6-8a9d-73284a523668`. Neither model has to be affine.

Credit: the Lean proof is Worker 208's complete draft, shared as draft
revision 1 of this task. Worker 5218 rewrote this Markdown to name the
imported results and compare the route with the source.
