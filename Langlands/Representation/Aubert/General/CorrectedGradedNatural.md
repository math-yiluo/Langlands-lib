# Naturality of the conditional surviving graded transitions

Module: `Langlands.Representation.Aubert.General.CorrectedGradedNatural`.

This module is a conditional (helper) result. It proves naturality in the
ambient smooth representation of the two maps built in
`CorrectedGradedReduction` at a surviving grade: the restriction `R_s` to the
new cell, and the graded map `β_s = Θ_s ∘ R_s` on the Jacquet module. The maps
along a morphism `φ : A ⟶ B` of smooth `G`-representations are the term map
`termMap φ s` (`i_J r_J φ`) and the step map `stepMap φ I s i`
(`r_I(i_J r_J φ)` restricted to step `i` of the corrected support filtration)
of `CorrectedFiltrationNatural`.

`R_s` is natural with no extra hypothesis. The orbit maps `Θ_s` are part of
the input data `OrbitJacquetData`, so naturality of `β_s` is proved under an
explicit hypothesis, `OrbitJacquetData.IsNatural`, that `Θ_s` is natural. This
module does not prove that hypothesis for any construction of
`OrbitJacquetData`. It does not construct an isomorphism between a graded
quotient of the filtration and the conjugated Jacquet module either. It also
does not prove the task target
`RationalPointFamily.RationalCorrectedGradedTransitionStatement`.

Provenance: the declarations are internal. They are the naturality in `E` of
the graded identifications of Aubert's erratum (Trans. AMS 348 (1996),
pp. 4688–4690, with the Ban–Jantzen double-coset correction), as cited in the
Markdown of `CorrectedFiltrationStatements`. The proofs only unfold the
published definitions of the restriction, the graded map, the term map and the
step map.

## Conventions

As in `CorrectedGradedReduction`: `J = S \ s` is `Finset.univ \ s`; `w : W`,
`m : G` and `K` are the parameters of `OrbitJacquetData`, with
`hK : ∀ x, x ∈ M I ↔ m⁻¹ x m ∈ M K`; the orbit piece is
`Geometric.orbitPiece (P J) (P I) m` of `inducingObject P M U h E J`. For a linear map `φ`, `[φ]` denotes
`Jacquet.Localization.mapLinear N 1 φ`, the map `[v] ↦ [φ v]` that `φ` induces
on `N`-coinvariants. In this module `N` is `U_J` or `U_K`.

## Declarations

Unconditional lemmas, for `φ : A ⟶ B`:

* `jacquetFunctor_map_hom`: the underlying linear map of the normalized Jacquet
  functor map `(jacquetFunctor hQ hN).map φ` is `[φ]` (by `rfl`).
* `termMap_eval`: `(termMap φ s f)(x) = [φ](f(x))` for every `x ∈ G`, with
  `[φ]` on `U_J`-coinvariants (by `rfl`).
* `stepSubrepresentationMap φ I s i`: `termMap φ s` as a function from
  `stepSubrepresentation … A I s i` to `stepSubrepresentation … B I s i` (the
  `P_I`-subrepresentations of functions supported in `G_{θ_i'}`), by
  `termMap_mem_inductionStep`.
* `stepRestriction_natural` (under `hPc` and
  `H : SurvivingSupportHypotheses P T cs I s i m`): for every `f` in step
  `i + 1` and every `q ∈ P_I`,
  `R_s^B (termMap φ s f)(q) = [φ](R_s^A f (q))`. Proof: both sides are
  evaluations of `f` at `m⁻¹ q` by `stepRestriction_eval`, and then
  `termMap_eval` applies.

The naturality hypothesis:

* `OrbitJacquetData.IsNatural DA DB φ`, for `DA` and `DB` of type
  `OrbitJacquetData P M U h hclosed hU T cs I A w m K hK` and
  `OrbitJacquetData P M U h hclosed hU T cs I B w m K hK`, is the proposition:
  for every `s` with `hKs : K ⊆ J` and `hs : IsMinimal cs J I w`, and all orbit
  functions `ψ` for `A` and `ψ'` for `B` with `ψ'(q) = [φ](ψ(q))` for every
  `q ∈ P_I`, we have `DB.Θ s hKs hs ψ' = [φ](DA.Θ s hKs hs ψ)`, with `[φ]` on
  `U_K`-coinvariants.

Under `hnat : DA.IsNatural DB φ`, with `hNc` for `I` and the other inputs of
`stepGradedMap`:

* `stepGradedMap_natural_apply`: for every `x` in step `i + 1` of
  `r_I(A_J)`,
  `β_s^B (stepMap φ I s (i + 1) x) = (Ad(m)(r_K φ)) (β_s^A x)`, where
  `Ad(m)(r_K φ)` is
  `(conjugationFunctor m hK).map ((jacquetFunctor (h K) (hclosed K)).map φ)`.
  Proof: write `x = [f]` with `f` in step `i + 1`. Then `stepMap` sends `x` to
  `[termMap φ s f]`, and `stepGradedMap_mk` gives
  `β_s^B [termMap φ s f] = DB.Θ (R_s^B (termMap φ s f))` and
  `β_s^A [f] = DA.Θ (R_s^A f)`. `hnat` applied to the two restrictions, with
  `stepRestriction_natural` as its premise, closes the proof.
* `stepGradedMap_natural`: the naturality square of morphisms of smooth
  `M_I`-representations

  ```
  stepMap T cs φ I s (i + 1) ≫ β_s^B = β_s^A ≫ (conjugationFunctor m hK).map
    ((jacquetFunctor (h K) (hclosed K)).map φ)
  ```

  It follows from `stepGradedMap_natural_apply` on underlying linear maps.

## Status

The module compiles with no errors or warnings, and has no proof holes or new
axioms. It sets `maxHeartbeats 800000` and
`backward.isDefEq.respectTransparency.types false`, as
`CorrectedGradedReduction` does. The naturality of `Θ_s` (the hypothesis
`IsNatural`) has to be proved separately for each construction of
`OrbitJacquetData`.
