# Conductors under norms and traces of unramified extensions

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It supplies
the common-exponent hypothesis of `BrauerKernel.UnramifiedKernel` in the situation
of the global argument's unramified places: the generator fields have the base
absolute ramification index, and the characters are unramified twists of a norm
pullback `α ∘ N_{L/E}`. The resulting relation-level statement is
`evaluationMap_eq_zero_of_unramified_normPullback`. The general kernel statement is
not claimed.

## Standalone local facts (`Langlands.PadicField.TopologicalData`)

Throughout, `F` and `E` are finite p-adic fields with a compatible algebra
`F → E`, and `T`, `S` are arbitrary supplied topological data. The hypothesis is
equality of absolute ramification indices, `T.ramificationIndex = S.ramificationIndex`,
which is the Library's unramified condition.

- `filtrationValuationIntegers` (imported from `UnitFiltrationConductor`): the normalized discrete valuation has `T.Integers` as
  its ring of integers in Mathlib's `Valuation.Integers` sense.
- `mem_maximalIdeal_pow_iff_discreteValuation_le`: an integer lies in `m^n` exactly
  when its valuation is at most `exp (-n)`. The Library's
  `maximalIdeal_eq_span_coordinateUniformizer` identifies `m^n` with the span of the
  `n`th power of the chosen uniformizer.
- `unitFiltration_eq_principalUnits`: the quotient-kernel filtration
  `T.unitFiltration n` of `ClassFieldTheory.Local.Units` equals the valuation filtration
  `T.principalUnits n` of `HarmonicAnalysis.Conductor`, at every level including zero.
  This is the content of the Library proposition
  `LocalClassField.UnitFiltrationComparison`, proved here pointwise as a helper. That
  Library proposition itself is not claimed.
- `map_normUnits_principalUnits`: under equal indices the norm maps `U_E^n` onto
  `U_F^n`. This is the published `LocalClassField.unramifiedUnitNorms`, translated by the
  comparison.
- `multiplicativeConductor_eq_of_comp_normUnits`: if `β = α ∘ N` pointwise, then
  `a(β) = a(α)`. Triviality at each level transfers along the surjection of the
  previous item, and the conductors are least trivial levels.
- `exists_trace_eq_of_ramificationIndex_eq` and `trace_mem_integers_of_mem`: under
  equal indices the field trace maps `S.Integers` onto `T.Integers`. The integer rings
  carry the published `relativeIntegerAlgebra` and the integral-closure and finiteness
  structure of `NYLL.relativeIntegerStructure`. Equal indices give
  `m_F O_E = m_E` (`map_maximalIdeal_algebraMap_of_ramificationIndex_eq_mul`), so
  `O_E / m_F O_E` is the residue field of `E`. The residue field extension is finite,
  hence separable, and its trace is nonzero (Mathlib's `Algebra.trace_ne_zero`).
  Mathlib's `Algebra.trace_quotient_eq_of_isDedekindDomain` identifies the residue trace
  with the reduction of `Algebra.intTrace`. So some integer has unit trace, and
  `Algebra.algebraMap_intTrace` turns integer traces into field traces. Integral
  elements have integral traces by the same identity.
- `ord_algebraMap_of_ramificationIndex_eq`: under equal indices the order of a base
  element is unchanged (from `ramificationIndex_mul_ord_relative_algebraMap`).
- `additiveConductor_traceCharacter_of_ramificationIndex_eq`:
  `n(ψ ∘ Tr_{E/F}) = n(ψ)`. With `u` the uniformizer of `F`, which has order one in `E`,
  the lattice of level `k` in each field is `u^{-k}` times its integers
  (`mul_mem_additiveLattice_iff`). Since the trace is `F`-linear and maps integers onto
  integers, triviality at level `k` agrees in the two fields.

## Common closure (`Langlands.LocalFactor.NonabelianBrauer`)

- `normPullback F e E L h α` is the field character of `L` whose Weil character is the
  restriction of the Weil character of `α`. It is the published
  `CommonClosureSpectralAnalytic.fieldCharacterEquiv` applied to that restriction.
- `normPullback_apply`: for normalized reciprocity, its value at `x` is
  `α(N_{L/E} x)`. This is the norm square of the normalized reciprocity premise, applied
  to the abelianized image of a Weil lift of `x`.
- `evaluationMap_eq_zero_of_unramified_normPullback`: let `presentationMap F e E z = 0`
  for a normalized family. Suppose every generator `g = (L, χ, χ')` of the support has
  `e_L = e_E`, and `χ = χ₀ · (α ∘ N)`, `χ' = χ₀' · (α ∘ N)` with `χ₀, χ₀'` unramified and
  one fixed `α`. Then `evaluationMap F E ψ measures z = 0`. The two preceding
  conductor identities give the common exponent `n(ψ) + a(α)`, and the published
  `evaluationMap_eq_zero_of_unramifiedTwist` applies.

The field universe `uF` and the representation universe `uV` are independent.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, Lemma 4.15
(printed page 545, PDF page 45) treats unramified data. There a character `ψ` with
`n(ψ) = 0` is chosen and the unramified trace and norm facts are used implicitly.
The facts proved here are the standard ones: `Tr(O_E) = O_F` and `N(U_E^n) = U_F^n`
for unramified extensions. They are internal derivations from Mathlib and the
published Library results named above.

The valuation witness and the equalities `mem_maximalIdeal_pow_iff_discreteValuation_le` and `unitFiltration_eq_principalUnits` are imported from `Langlands.ClassFieldTheory.Local.UnitFiltrationConductor`.
