# Strict scalar normalization descends rational ideal effectiveness

This module proves
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover.StrictScalarIdealDescentStatement`
as the theorem `strictScalarIdealDescent`. Assume the strict theorem
`StrictRationalIdealEffectivenessStatement`. Then the general theorem
`RationalIdealEffectivenessStatement` holds over every complete ultrametric
field `K`, for every presented affinoid algebra `A` with positive polyradius,
every finite cover by rational charts `D : Fin n → RationalChart K A`, and every
family of closed local ideals `I i` that is compatible on the full-domain
intersections. Its conclusion is the original equation
`(D i).baseMap.closedIdealMap ((ofRationalCharts D hD).idealContraction I) = I i`.
This equation is stated for the original actual quotient norms and the explicit
contraction `⋂ j, comap (D j).baseMap (I j)`. No hypothesis is added. The proof
makes no case split on `n`, on the spectrum, or on whether an algebra is zero or
reduced, so it covers empty covers, empty spectra and zero or nonreduced
algebras.

The route follows the reduction of Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), after Kiehl's Theorem and in
Remark 1.2.1(ii): extend scalars until the field is nontrivially valued and all
radii are values of the norm, apply the strict theorem, and descend. The Lean
descent step is specific to ideals. It does not use an equalizer of modules.
It uses a bounded coefficient retraction and a density argument. Each step is
listed below.

## 1. The scalar extension (`strictScalarIdealDescent`)

Let `D'` be the family indexed by `Fin n ⊕ (Fin n × Fin n)` that sends `inl j`
to `D j` and `inr (j, k)` to the rational intersection chart
`(D j).inter (D k)`. The radius family is
`t = Sum.elim (familyRadius D') (fun _ => 2)`. It lists every base radius of
`A`, every relative radius of each chart `D j` and of each intersection chart,
and one extra radius `2`. All of these radii are positive, so
`FiniteRadiusRealization.nonempty` gives the following data:

- a complete ultrametric field `L : Type u` and an isometric embedding
  `ι : K →+* L`;
- elements `cc s` of `L` with `‖cc s‖ = t s`;
- an additive retraction `π : L →+ K` with `π (ι a * x) = a * π x`,
  `π 1 = 1` and `‖π x‖ ≤ B * ‖x‖`.

The extra coordinate satisfies `‖cc (inr ())‖ = 2 > 1`. So `L` is nontrivially
normed, as the strict premise requires, even when `K` has the trivial
valuation. The coordinates of the other radii give
`c` (the base), `τ j` (chart `D j`) and `υ (j, k)` (chart `(D j).inter (D k)`).
All remaining work happens in `rationalIdealEffective_of_realization`, which
takes these data as input.

## 2. Strict local ideals and the strict cover

The Library's strict scalar extension `strictBaseChange A ι hι hc` is a strict
affinoid algebra over `L`, with the bounded map `strictBaseChangeHom` (norm
at most one). Write `δ j = (D j).scalarNormalizedStrict ι hι hc (hτ j)` for the
normalized strict rational data of `D j` over this base, and
`F_j = (D j).scalarNormalizedStrictMap`, which is `normalizedStrictMap` for
the strict base change, mapping `(D j).algebra → (δ j).algebra`. The strict
local ideals are

`I' j = closure (Ideal.map F_j (I j))`.

They are closed by construction, so no separate closedness theorem is used.
`RationalChart.normalizedStrict_cover` shows that the loci of the `δ j` cover
the spectrum of the strict base.

## 3. Compatibility on strict intersections (Overlap section)

The strict premise asks for compatibility along the actual strict intersection
restrictions `interLeft (δ j) (δ k)` and `interRight (δ j) (δ k)`. The proof
builds its own comparison map from the original full-domain intersection
`(D j).toDomain.inter (D k).toDomain` to the strict intersection
`(δ j).inter (δ k)`. It is the composite `scalarOverlapMap` of three maps:

1. `interChartInclusion`: the restriction `Domain.inclusionOfSubset` from the
   full-domain intersection to the rational intersection chart
   `(D j).inter (D k)`. It exists because `locus_inter` gives the two loci as
   equal.
2. `normalizedStrictMap` of the intersection chart, using the coordinates
   `υ (j, k)`.
3. The strict restriction `normalizedInterInclusion` from the normalized
   intersection chart to the strict intersection `(δ j).inter (δ k)`. Its locus
   inclusion is `normalizedStrict_inter_subset`: by
   `StrictTestDomain.RationalData.locus_inter`, `normalizedStrict_locus` and
   `locus_inter`, both loci are the preimage of `(D j).locus ∩ (D k).locus`.

`scalarOverlapMap_baseMap` shows that this composite sends the base image of
`a : A` to the strict intersection's base image of `strictBaseChangeHom a`.
Both squares

- `scalarOverlapMap ∘ interLeft = interLeft(δ j, δ k) ∘ F_j`
  (`scalarOverlapMap_interLeft`), and
- `scalarOverlapMap ∘ interRight = interRight(δ j, δ k) ∘ F_k`
  (`scalarOverlapMap_interRight`)

are equalities of bounded ring maps out of the chart algebra. They follow from
`RationalChart.ringHom_ext_over_base`, because both sides agree on the image of
the base: they are bounded maps that agree on `baseMap`.

Next comes the abstract lemma `StrictScalarIdealDescent.closure_map_compatible`.
For continuous ring maps `md, me, G` with `md ∘ Fd = G ∘ l` and
`me ∘ Fe = G ∘ r`, the equation `closure (map l Id) = closure (map r Ie)`
implies `closure (map md (closure (map Fd Id))) = closure (map me (closure (map Fe Ie)))`.
The proof applies `topologicalClosure_map_topologicalClosure` (closing before or
after extending along a continuous map gives the same closed ideal) and
`Ideal.map_map`. With these inputs it gives
`normalizedStrict_closedIdealMap_compatible`: compatibility of the original
`I j`, `I k` along the actual full-domain restrictions gives the strict premise's
compatibility for `I' j`, `I' k`. Continuity of bounded maps comes from
`BoundedAlgHom.continuous` and `continuous_boundedRingHom`.

## 4. Applying the strict theorem

The strict premise applies to `L`, the strict base, `δ`, the cover, `I'`, its
closedness and its compatibility. It gives, for every `i`,

`(δ i).baseMap.closedIdealMap J = I' i`, where `J = ⋂ j, comap (δ j).baseMap (I' j)`.

## 5. Retraction of `J` into the original contraction

The chart retraction `ρ_j = (D j).scalarRetraction` maps
`(δ j).algebra →+ (D j).algebra`. It is the bounded comparison `scalarComparison`
followed by the module retraction `strictBaseChangeRetraction`. Three facts
about it are proved here:

- `continuous_scalarRetraction`: it is continuous, because the retraction is
  bounded (`norm_strictBaseChangeRetraction_le`) and the comparison is a
  bounded algebra map.
- `scalarRetraction_scalarNormalizedStrictMap_mul`: it is linear over `F_j`,
  meaning `ρ_j (F_j a * b) = a * ρ_j b`. The proof uses
  `scalarComparison_comp_map`, which identifies `scalarComparison ∘ F_j` with
  the strict base change map of `(D j).algebra`, together with
  `strictBaseChangeRetraction_strictBaseChangeHom_mul`.
- `scalarRetraction_baseMap` (Library): it carries the base image of `q` to
  `(D j).baseMap (π_A q)`, where `π_A = strictBaseChangeRetraction A`.

The abstract lemma `retract_mem_of_mem_closure_map` is proved by the closed
ideal `retractIdeal ρ M = {y | ∀ b, ρ (b * y) ∈ M}`. It shows that a continuous
`F`-linear additive map sends `closure (map F I)` into `I` whenever `I` is
closed. Take `q ∈ J`. Then `(δ j).baseMap q ∈ I' j`, so
`(D j).baseMap (π_A q) ∈ I j` for every `j`. By `mem_idealContraction`, this
says `π_A q` lies in the original explicit contraction
`(ofRationalCharts D hD).idealContraction I`.

## 6. Local descent through density

The containment `closedIdealMap (contraction) ≤ I i` is the Library lemma
`closedIdealMap_idealContraction_le`. For the reverse containment, let
`M = (D i).baseMap.closedIdealMap (contraction)`. It is a closed ideal of
`(D i).algebra`, and by step 5 and `mem_closedIdealMap` it contains
`ρ_i ((δ i).baseMap q)` for all `q ∈ J`. The abstract lemma
`le_of_closure_map_eq` then gives `I i ≤ M`. It uses:

- the strict equation `closure (map β J) = closure (map F_i (I i))` from
  step 4, where `β = (δ i).baseMap`;
- `ρ_i (F_i a) = a` (Library `scalarRetraction_map`, using `π 1 = 1`);
- an element `w` with `F_i w * β s = 1`, where `s` is the strict denominator
  (`exists_scalarNormalizedStrictMap_mul_denominator`). Here `w` is a left
  inverse of the original denominator in `(D i).algebra`
  (`RationalPresentation.isUnit_baseMap_denominator`), pushed forward by `F_i`;
- density of the fraction set `{x | ∃ r a, β s ^ r * x = β a}` in
  `(δ i).algebra`. This is the Library's
  `StrictTestDomain.RationalData.dense_fractionSubalgebra`.

The argument runs as follows. For `x ∈ I i`, `F_i x` lies in
`closure (map β J)`. The set of `y` with `ρ_i (b * y) ∈ M` for all `b` is a
closed ideal, so it suffices to put each `β q`, `q ∈ J`, into it
(`retract_mul_mem_of_dense`). For a fraction `b` with `β s ^ r * b = β a`, we
have `b = F_i (w ^ r) * β a`. Then `F_i`-linearity gives
`ρ_i (b * β q) = w ^ r * ρ_i (β (a * q)) ∈ M`. The set of such `b` is
contained in a closed set and is dense, so the condition holds for all `b`.
Taking `b = 1` and applying `ρ_i (F_i x) = x` gives `x ∈ M`. Antisymmetry
finishes the proof.

## Scope

The theorem is exactly the Library statement. The strict premise is used once,
over the realized field `L` in universe `u`. The proof uses no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.
