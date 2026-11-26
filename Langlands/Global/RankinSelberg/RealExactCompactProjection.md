# Compact averages of translates for real Whittaker intertwiners

`RealExactCompactProjectionStatement` concerns a real block list `ds`, the
`O(r+1)`-finite real standard module `Automorphic.realStandardKFinite (r + 1) ds`
and an arbitrary specified real Whittaker intertwiner `B`
(`IsRealWhittakerIntertwiner r ds a B`). No continuity of `B` and no uniform growth
exponent is assumed. Fix a Haar measure `ν` on `O(r+1)` (with its Borel structure)
and a continuous weight `κ` on `O(r+1)` whose left translates `k ↦ κ(h⁻¹ k)` span a
finite-dimensional space. For every standard vector `f` and every `g ∈ GL_(r+1)(ℝ)`
the statement gives a standard vector `p` with

* `p(x) = ∫ κ(k) f(x k g) dν(k)` for every `x`, and
* `B p (x) = ∫ κ(k) B f (x k g) dν(k)` for every `x`.

So compact convolution of a genuine right translate of a compact-finite vector is again
compact-finite, and every intertwiner of the specified kind commutes with this operation.
`realExactCompactProjection` proves it. It is the real counterpart of the Library theorem
`complexWhittakerCompactProjection` (module `ComplexLocalWhittakerGrowth`); the earlier
real module `RealWhittakerCompactProjection` proves a related separation under the
additional hypothesis that `B` is realized by a continuous Whittaker evaluation.

## Proof

The proof works at the real place `v` of the number field `ℚ` and uses the Library's
smooth-function theory on the archimedean group `A = GL_(r+1)(ℚ ⊗ ℝ)`.

1. **Transport.** Let `π : A → GL_(r+1)(ℝ)` be the projection to the coordinate at `v`
   and `ι` the insertion of a real matrix at `v` (identities elsewhere); `π ∘ ι` is the
   identity (`projection_inclusion`, from the coordinates of `realPlaceGL`). Pulling a
   smooth function `W` back along `π` gives a smooth function on `A` (the matrix chart
   of `π` is a real algebra map). Its right derivative in a direction `X` of the real Lie
   algebra of `A` is the pullback of the right derivative of `W` in the projected direction
   (`pullback_differential`, chain rule on the units extension).
2. **The pair family.** For a standard vector `f`, `liftPair f` is the family indexed by
   `Bool` whose `false` entry is the pullback of `f` and whose `true` entry is the pullback
   of `B f`. Right translation by an element `k` of the standard compact subgroup of `A`
   becomes the action of its projection in `O(r+1)` on `f`
   (`liftStandard_compact`, `coefficients_compact`; the latter uses the compact
   equivariance clause of `IsRealWhittakerIntertwiner`). The enveloping algebra of `A`
   acts through the projected enveloping algebra of the real standard module
   (`enveloping_of_lie`, by induction on enveloping elements from the Lie compatibility of
   `realStandardLie` and the Lie clause of `IsRealWhittakerIntertwiner`).
3. **Finiteness.** The range `Q` of `liftPair` is stable under the compact and enveloping
   actions, and each of its vectors has a finite-dimensional compact orbit span, coming
   from the admissibility of the real standard `(𝔤, K)` module. Each pulled-back function
   is jointly finite (`jointFinite_of`): the centre of the enveloping algebra acts by
   scalars because the projection of a central element is central and the real standard
   module has an infinitesimal character (`realStandardLie_hasInfinitesimalCharacter`),
   and compact finiteness gives differential finiteness
   (`compactGroupFiniteDifferential`).
4. **Finite rank of the average.** Let `P` be the compact average with weight `κ` along the
   inclusion of `O(r+1)` at `v`. Averages of vectors of `Q` lie in the closure of a
   finite-dimensional compact orbit span inside `Q`, hence in `Q`. Evaluation of the
   `false` entries on `O(r+1)` is injective on `Q`, because a principal-series function is
   determined by its restriction to the orthogonal group
   (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`). The finite separated expansion
   `κ(x⁻¹ k) = ∑ α_l(x) β_l(k)` of the weight
   (`hasFiniteCompactConvolutionKernel_of_finite_translates`) puts these evaluations of
   `P(Q)` in the span of the finitely many `α_l`, so `P(Q)` is finite-dimensional.
5. **Translation.** The Library's `averagedTranslate_mem` (module
   `ArchimedeanCompactAverageTranslation`) now shows that the average of the simultaneous
   translate of `liftPair f` by `ι(g)` lies in `Q`, say equal to `liftPair p`. Evaluating
   both entries at `ι(x)` and using `π ∘ ι = id` gives the two displayed identities.

The final theorem specializes to `F = ℚ` and its real infinite place.

## Provenance

This is an internal analytic lemma for the real Rankin–Selberg integrals. It formalizes the
compact projection of a translated inducing vector used by Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), §8.2–§8.3, pp. 56–60, in the real case and for the
Library's specified intertwiners, without any continuity hypothesis on them.
