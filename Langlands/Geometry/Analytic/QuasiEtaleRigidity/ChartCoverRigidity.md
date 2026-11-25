# Rigidity from rigidity on the charts of a finite chart cover

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It is internal.

## Helpers

- `pullback_congr`: equal strong maps have equal pullbacks.
- `localizedSpaceFunctor_map_apply`, `mem_of_baseMap_mem`: points of the
  localized space of a strong map.
- `isNear_lift_of_strongNear`: let `a`, `b` be strong maps into an analytic
  domain `D` with lifts `ξa`, `ξb` through `D`. If `a` and `b` are near for the
  ambient triple of a test triple `τ` of `D`, then `IsNear τ ξa ξb`. Common
  numerators of the lifts recompose to `t ≫ a` and `t ≫ b` by faithfulness.
  The Library's `strongNear_comp_domainInclusion_iff` then applies.
- `chartTestTriple A i`: the triple with the domain of chart `i`, function `0`
  and bound `1`. It controls preimages of the chart.
- `pullback_eq_of_isRigidOn_chart`: suppose the restriction
  `incl_i ≫ map g` of `g` to a chart `i` is rigid with test triples `E`. Let
  `x₁ ≫ g = x₂ ≫ g`, and let `x₀, x₁, x₂` be near for the ambient triples of
  `E`. Then the pullbacks of `x₁` and `x₂` agree on every source chart `P`
  mapped into `i` by all three. The proof lifts `ι_P ≫ xₖ` through the chart
  domain with `exists_localizedDomainLift`, applies rigidity, uses
  faithfulness to get `ι_P ≫ x₁ = ι_P ≫ x₂`, and finishes with
  `domainInclusion_comp_pullback`.
- `comp_eq_of_numerators` and `eq_of_numerators`: transfer equalities between
  localized arrows and their strong numerators.

## Main result

`isRigidOn_of_chart_cover`: let the space of `A` be Hausdorff, let finitely many
charts `s` cover it, and let `incl_i ≫ map g` be rigid on its whole source for
every `i ∈ s`. Then `map g` is rigid on the whole space. The test triples are
the ambient triples of the chart rigidities together with the chart triples.
The proof merges witnesses (`exists_strongNear_numerators`), derives
`x₁ ≫ g = x₂ ≫ g`, and applies `localizationFunctor_map_eq_of_local_eq` with
`L = univ`, using `pullback_eq_of_isRigidOn_chart` on good charts.
