# Finite completions of number fields as p-adic fields

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1 (contract item 3: the
local-to-global link between number-field completions and the local
objects). Worker 2, who owns the global adelic interface (task `6c50b2fd`),
agreed that this bridge belongs here. Worker 50 owns the completion maps
and local norms used below.

## Purpose

The local factors in `Langlands.LocalFactor` are stated over
`PadicField.TopologicalData`. That is a finite extension `F` of Mathlib's
`Padic p` together with a topology, a valuative relation and local-field
certificates. The global objects in `Langlands.Global` use Mathlib's
completions `v.adicCompletion K` of a number field `K` at a finite place
`v : HeightOneSpectrum (𝓞 K)`. Before this module the Library had no map
from the second kind of object to the first. Global functional
equations, local components of Hecke characters and the
local-to-global realization statements all need it.

This module constructs that map. Its topology is the completion's own
topology, not a new one, and the module proves that its valuation is
equivalent to the completion's valuation.

## Constructions

Fix `K : Type u` with `[Field K] [NumberField K]` and a finite place `v`.

- `rationalPlace v : HeightOneSpectrum (𝓞 ℚ)` is Mathlib's
  `v.under (𝓞 ℚ)`, the contraction of `v` to the integers of `ℚ`. The
  instance `liesOver_rationalPlace` records `v.asIdeal.LiesOver
  (rationalPlace v).asIdeal`. It is Mathlib's `Ideal.over_under`. It is
  restated because instance search does not unfold
  `HeightOneSpectrum.under`.
- `residuePrime v : ℕ` is `Rat.HeightOneSpectrum.primesEquiv
  (rationalPlace v)`, the positive generator `p` of `v ∩ ℤ`. It is the
  characteristic of the residue field of `v`. The instance
  `residuePrime_fact` provides `Fact (residuePrime v).Prime`. It is an
  `abbrev` of type `ℕ`, so `Padic (residuePrime v)` is the usual `ℚ_p`.
- `padicMap v : Padic (residuePrime v) →+* v.adicCompletion K` is the
  composite of two existing maps. The first is the inverse of Mathlib's
  continuous `ℚ`-algebra isomorphism
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)`
  from the completion of `ℚ` at `rationalPlace v` to `ℚ_p`. The second
  is Worker 50's published
  `AdelicFunctoriality.FiniteExtension.completionMap (rationalPlace v) v`.
  That map is the completion of the field inclusion `ℚ → K` at a prime
  over a prime. `continuous_padicMap` proves continuity from the
  continuity of both factors. Every ring homomorphism between fields of
  characteristic zero fixes `ℚ`, and `ℚ` is dense in `ℚ_p`. Hence
  `padicMap v` is the only continuous ring homomorphism
  `ℚ_p → v.adicCompletion K`. This uniqueness is a remark, not a
  formalized theorem.
- `padicAlgebra v` is `(padicMap v).toAlgebra`. It is a definition, not a
  global instance. Mathlib already puts other algebra structures on
  `v.adicCompletion K`, over `K` and over `ℚ`. A global `ℚ_p`-algebra
  instance would let instance search find it in unrelated contexts.
  Consumers obtain it through `padicField v`, or locally with
  `letI := padicAlgebra v`.
- `padicFinite v` proves `FiniteDimensional ℚ_p (v.adicCompletion K)`
  for this algebra. It transports Worker 50's `local_finite` (finiteness
  over the completion of `ℚ`) along `padicEquiv` with
  `Module.Finite.of_equiv_equiv`. The required commuting square holds
  because `padicEquiv.symm (padicEquiv x) = x`.
- `padicField v : PadicField.{u} (residuePrime v)` has carrier
  `v.adicCompletion K`, algebra `padicAlgebra v` and finiteness
  `padicFinite v`. The universe is that of `K`.
- `topologicalData v : (padicField v).TopologicalData` is the local-field
  realization:
  - `topology` is the completion topology
    `inferInstanceAs (TopologicalSpace (v.adicCompletion K))`.
    `topologicalData_topology` states this and is proved by `rfl`.
  - `valuativeRel` and `valuativeExtension` are those of the published
    `(padicField v).canonicalTopologicalData`, which come from the
    spectral norm.
  - `moduleTopology` is `completion_isModuleTopology v`.
  - `localField` is the certificate of `canonicalTopologicalData`,
    rewritten along `completion_topology_eq v`.

## Proved comparisons

- `completion_isModuleTopology`: with `padicAlgebra v`, the completion
  topology is the `ℚ_p`-module topology. Scalar multiplication is
  continuous because `padicMap v` is continuous. The completion is then a
  finite-dimensional Hausdorff topological vector space over the complete
  field `ℚ_p`, and Mathlib's `isModuleTopologyOfFiniteDimensional`
  applies. This is the uniqueness of the vector-space topology used by
  Serre, II §2, Prop. 3.
- `completion_topology_eq`: the completion topology equals
  `(padicField v).canonicalTopologicalData.topology`. The latter is the
  module topology by the published `canonicalTopologicalData_topology`,
  and `eq_moduleTopology` concludes.
- `valued_lt_one_iff` and `valued_isEquiv`: the completion's valuation
  `Valued.v`, with values in `ℤᵐ⁰`, is equivalent to the published
  `(padicField v).canonicalValuation`. The proof follows Serre's argument
  in II §2, Prop. 3, which recovers a valuation from its topology. For
  each of the two valuations, `x` has absolute value less than one
  exactly when `x ^ n → 0`. For the completion this is Mathlib's normed
  field `Valued.toNormedField`. For the spectral norm it is the helper
  `norm_lt_one_iff_tendsto_pow`, applied to the explicit instance
  `(padicField v).canonicalNormedField.toNormedField`. The two limits are
  taken in the same topology by `completion_topology_eq`. Then
  `Valuation.isEquiv_iff_val_lt_one` gives the equivalence.
- `mem_adicCompletionIntegers_iff`: an element lies in
  `v.adicCompletionIntegers K` exactly when its spectral norm is at most
  one. So the integers of `topologicalData v` are Mathlib's completed
  integers.
- `topologicalData_vle`: the valuative relation of `topologicalData v` is
  `Valued.v x ≤ Valued.v y`. So the valuation of the local-field
  realization is, up to equivalence, the completion's own valuation.

These comparisons concern the equivalence class of the valuation only.
The spectral norm extends the usual absolute value of `ℚ_p`. It is not
the normalized absolute value of `K_v`, which depends on the residue
cardinality (Serre, II §1, p.27). Statements that need the normalized
absolute value must say so separately.

## Implementation notes

- The module opens the scoped instances of
  `Langlands.Global.AdelicFunctoriality.FiniteExtension`. They supply the
  completion-algebra structure that `local_finite` is stated with. No new
  scoped or global algebra instance is declared.
- `canonicalNormedField` is an explicit spectral structure, not an
  instance. Mathlib also has a global normed field on
  `v.adicCompletion K` that comes from the adic valuation
  (`instNormedFieldValuedAdicCompletion`, in
  `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`). The proof of
  `valued_lt_one_iff` therefore passes the spectral instance explicitly.
  A `let` binding would lose to the global instance.

## Provenance

Derived. Each mathematical ingredient is standard. The completion of a
number field at a finite place is a finite extension of `ℚ_p`. Its
valuation is the unique one extending the `p`-adic valuation. Its
topology is the topology of a finite-dimensional `ℚ_p`-vector space. See
Serre, *Local Fields* (1979), Chapter II, Section 2, Proposition 3 and
Corollary 2, printed pp.28-29 (PDF pp.36-37), and Section 3,
Theorem 1 (i)-(ii), printed pp.30-31 (PDF pp.38-39). The packaging into
the Library's `PadicField` and `PadicField.TopologicalData` interfaces is
internal to this project.

Dependencies:

- Mathlib `Rat.HeightOneSpectrum.primesEquiv` and
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`
  (`Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean`).
- `Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap`,
  `continuous_completionMap` and `local_finite` (Worker 50,
  `Langlands/Global/AdelicFunctoriality/Extension.lean`).
- `Langlands.PadicField`, `canonicalTopologicalData`,
  `canonicalTopologicalData_topology`, `canonicalTopologicalData_vle` and
  `canonicalValuation_coe` (`Langlands/LocalField/`).
