# Abelian epsilon expressions

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Abelian.Definitions`.
It is moved from `Langlands.LocalFactor.Abelian` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
Worker 20 authored the original construction; Worker 64 authored only this migration.
The [migration record](Definitions.md#structural-migration-record) gives the complete map and checks.


This module constructs Tate's measure-dependent abelian epsilon expression
on an actual finite extension of `Q_p`, with a supplied local-field topology,
continuous multiplicative quasicharacter, continuous nontrivial unitary additive
character, and regular additive Haar measure. Both the unramified formula and
the convergent ramified integral are implemented. This module belongs to the
coherent construction contribution with `Conductor` and `PadicAbelian`.
Its external harmonic prerequisite is published in the current Library.

The source is Tate, *Number theoretic background* (1979), section 3.2.6,
printed pages 13–14 (retained PDF pages 22–23). The additive conductor is
the largest integer of triviality on `π^(-n) O`; the multiplicative conductor
is the least unit-congruence level, with zero in the unramified case.
Writing `n=n(ψ)`, `a=a(χ)`, and choosing `ord(c)=n+a`, the original formulas
(3.2.6.1) and (3.2.6.2) give

```
a = 0:  ε(χ,ψ,dx) = χ(c) / |c| · vol_dx(O),
a > 0:  ε(χ,ψ,dx) = ∫_{c⁻¹ Oˣ} χ(x)⁻¹ ψ(x) dx.
```

The additive character has the plus sign. The absolute value is
`|x|=q^(-ord(x))` for nonzero `x`, with `q` the cardinality of the actual residue
field. These are constants for the given quasicharacter; this module does not
silently insert a spectral twist or Langlands' half shift. The two original
pages have been visually read.

Registered original: `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

The Lean function `Quasicharacter.extendZero` extends the actual character
from field units to the field by assigning zero only at zero. On the nonzero
subspace it remains continuous and nonzero. The integrand uses its complex
reciprocal times the original additive character, with a plus sign.
The actual `valuationShell k` has discrete value `exp(k)`, hence order `-k`.
The proof of compactness identifies it with a fiber of the underlying
valuation, proves that fiber closed, and places it inside a compact valuation
ball. The fiber is disjoint from zero. Consequently the integrand is continuous
on `epsilonShell χ ψ = valuationShell (n+a)`, and
`epsilonIntegrand_integrable` proves its additive-Haar integrability there.
`abelianGaussIntegral` is that set integral. This construction does not rely on
the total Bochner integral's fallback for nonintegrable functions.

`abelianScale k` is a unit chosen from a proved existence statement using
surjectivity of the actual local-field valuation. Its valuation and order are
proved, rather than postulated. The shell identity
`mem_valuationShell_iff_scaled_integral_unit` identifies the shell with
`(abelianScale k)⁻¹ Oˣ` on field units. The denominator in the unramified
expression is strictly positive: the residue field is finite and nonempty,
so its cardinality is positive and every integer power of that cardinality
is positive. `integerVolume` is the real-valued measure of the actual integer
ring; `integerVolume_measure_ne_top` proves finiteness from compactness.

`abelianEpsilonExpression` selects the unramified expression when `a=0` and
the Gauss integral otherwise. The branch lemmas use the proved equivalence
between conductor zero and triviality on integral units. The unramified
expression is independent of its allowed scale choice: the quotient of two
units with the same valuation is an integral unit, on which an unramified
character is one. Their normalized absolute values are also equal.
`abelianEpsilonExpression_unramified_scale` supplies the resulting formula
for every unit with the required valuation. The ramified definition uses
the intrinsic valuation shell directly and makes no scale choice.

The result is a constructed complex number, not yet a bundled complex unit.
Nonvanishing and identification by the functional equation remain separate
theorem obligations. No nonabelian constant system, reciprocity map, or
self-dual measure is assumed. In particular, this does not construct an
unconditional nonabelian epsilon function.

The direct project dependency is `Langlands.HarmonicAnalysis.Conductor`.
It supplies proved additive and multiplicative conductors, actual valuation
lattices, and integral-unit criteria. Its upstream imports are
`Langlands.LocalField.Definitions`,
`Langlands.LocalField.Normalization.Definitions`,
`Langlands.Representation.Twist.ContinuousCharacterProof`, and
`Langlands.HarmonicAnalysis.Basic`, all present in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
The conductor pair is included in the same coherent contribution.

The remaining construction proofs use the pinned Mathlib local-field,
valuation, topological-unit, and Bochner-integration APIs. In particular,
`Units.isEmbedding_val₀` identifies the nonzero field subspace with its unit
group, `IsNonarchimedeanLocalField.isCompact_closedBall` gives compactness,
and `ContinuousOn.integrableOn_compact'` supplies the integral's convergence.
These are intrinsic implementation proofs, not a claim to have formalized
Tate's functional equation.

## Structural migration record

Worker 64 performed this path-only migration for task
`8be3987f-f024-440f-a653-00af0dc5f79d`, revision 1. The refreshed base is
Library `30ceb5a0d89d8094c1663fc19f35416519b9a125`: 269 Lean modules,
each with nonempty same-stem Markdown. Before editing, the workspace matched
that base byte for byte and none of the eight destinations existed. The
contribution adds eight canonical modules, for 277 modules in the checked tree,
and edits the nine existing pairs listed below. It retains Workers 20 and 33's
original mathematical authorship and all original source references. Worker 64
owns the path migration and its verification, and asserts no new mathematics.
Historical validation/status paragraphs in the moved documentation describe the
original submissions; migration acceptance and publication are tracked separately.

### Module and declaration map

The following paths are relative to `Langlands/`; each row applies to both
`.lean` and `.md`. Each old Lean path contains exactly one import of its new
module, and its Markdown links to the canonical documentation. All public
Lean declaration names map **to themselves**, including their namespace
prefixes. There is no alias declaration or second definition of any object.

| Old module path | Canonical module path |
| --- | --- |
| `LocalFactor/Abelian` | [`LocalFactor/Abelian/Definitions`](Definitions.md) |
| `LocalFactor/PadicAbelian` | [`LocalFactor/Abelian/Padic`](Padic.md) |
| `LocalFactor/ReciprocalEntire` | [`LocalFactor/Analytic/ReciprocalEntire`](../Analytic/ReciprocalEntire.md) |
| `LocalFactor/Archimedean` | [`LocalFactor/Archimedean/Definitions`](../Archimedean/Definitions.md) |
| `LocalFactor/ArchimedeanStatement` | [`LocalFactor/Archimedean/Statement`](../Archimedean/Statement.md) |
| `LocalFactor/Euler` | [`LocalFactor/Euler/Definitions`](../Euler/Definitions.md) |
| `LocalFactor/EulerStatement` | [`LocalFactor/Euler/Statement`](../Euler/Statement.md) |
| `LocalFactors/Harmonic/Statement` | [`LocalFactor/Harmonic/Statement`](../Harmonic/Statement.md) |

`Langlands.LocalFactor.PadicAbelianStatement` stays at its existing path;
its sole project import becomes `Langlands.LocalFactor.Abelian.Padic`.
The other three base import edges become
`Abelian.Padic → Abelian.Definitions`,
`Archimedean.Definitions → Analytic.ReciprocalEntire`, and
`Euler.Statement → Euler.Definitions`, all under `Langlands.LocalFactor`.
The complete checked tree has no imports of the eight old modules. Every Lean
file has a nonempty same-stem Markdown file, and all new relative Markdown links
resolve. Module references in the moved docs and the unchanged-path statement
are updated; historical source fingerprints are labeled as historical.

The following namespaces intentionally remain unchanged:
`Langlands.HarmonicAnalysis.Quasicharacter`,
`Langlands.PadicField.TopologicalData`,
`Langlands.LocalFactor`, `Langlands.LocalFactor.PadicAbelian`,
`Langlands.LocalFactor.ReciprocalEntire`,
`Langlands.LocalFactor.Archimedean` (including `GammaBlock`), and
**`Langlands.LocalFactors`** for the harmonic statements. In particular,
`Langlands.LocalFactors.PadicHarmonicAnalysisStatement` keeps its plural
namespace although its module moves to the singular root.

The separate regular-point types remain separate. Gamma representatives,
punctured germs, values at poles, spectral arguments, epsilon normalizations,
universe parameters, implicit arguments and intrinsic proofs are retained.
`LocalFactor/Ramification`, `HarmonicAnalysis` and the representation-side
Rankin–Selberg/JPSS trees are untouched. This contribution proves no previously
unproved local functional equation.

### Source preservation

For every row below, remove only lines beginning with the ASCII bytes
`import `, retaining every other byte, including line endings. The SHA-256
of the resulting old and canonical Lean byte sequences is identical. This
checks the complete definition bodies, proposition bodies, proofs, declaration
commands, attributes, variable declarations and namespaces, rather than only
selected closing declarations. The last row is the unchanged-path importer.

| Base module (prefix `Langlands.` omitted) | Identical non-import SHA-256 | Canonical complete Lean SHA-256 |
| --- | --- | --- |
| `LocalFactor.Abelian` | `22d0ad4cbd623d8bb6dcaa56d621018bc5cad05d9f58aff7d930273205326302` | `18215959be4fdf7359708f2250aa94e60a3a78f6e99919ea0c7ada61cf74ba22` |
| `LocalFactor.PadicAbelian` | `f7268e253540a029c20d04909f2438c7d4413e0aa711488b08da91edae5e5745` | `52c2257f1eb2963461a5bf98ee771680f8e2e9368a09328d349cac97ec34bb11` |
| `LocalFactor.ReciprocalEntire` | `15161b25daa0e781ebae95f6f3e4bad092c1652287dc92ae67b19d8a9cc318cf` | `6a356d1ac936d0b70c91f256eb7ceb3ac74e5868a9e563d01058734e82024830` |
| `LocalFactor.Archimedean` | `c52079f4ca3403d7a5a2197aded2005c5792c9080c4c2eb8e6caa57e4aa82a23` | `c3a00377a5ca918a2c27c474bde2908ba07a5329455b521297fa841c5e3d58fc` |
| `LocalFactor.ArchimedeanStatement` | `b0563cc1fb7704b96b2102ee2254b1076a1932313673b70ada4e18bcda8ac648` | `74cadb41bd41cc98e3dd5a6921963393ca96470154d6ddd94c618ef401c4e80c` |
| `LocalFactor.Euler` | `d7b1292ab0fdfd9c2ab6747a5390969d7fb235ca6d62cc181e616d017316dd04` | `6fde12cbc1ed3f8e6e184468f5edab01cf1e597256f06234e0e6d675f1ba617d` |
| `LocalFactor.EulerStatement` | `358a3729c3c2c78ce8b4a8132f71eebf7967893b70cd3febc098c9cf1728d407` | `834004540ff5525c8e46d1e710ae6a933259c8b3a56ac0c85335656d33cbeede` |
| `LocalFactors.Harmonic.Statement` | `7d4342f95cafc9c2a5b191dd51a0dc4026c1b01815af115aeaa8e6d5d69cb852` | `1daa8305602e7162c20fe612295f15403e02df81128bc299cdcd7d17becd13c3` |
| `LocalFactor.PadicAbelianStatement` | `c451ebb492a138b6e6ae977aca3ffcb24cc9e41c2609e340604ea87f0e361f73` | `2cca7ebf5c5e2e19580e174fddbc772e89f623c5cccb6fb92db7b24e8592cfc7` |

### Complete declaration and target checks

Baseline check `71b52e81-3ada-45e1-9e5f-035db0d9a6ad` built all nine
affected modules and inspected `PadicAbelianLocalAnalysisStatement` successfully.
Private inspection `2d1c5b26-9eb2-45dd-8507-54b16cf391b4` recorded every
non-private constant owned by those modules: **307 public declarations**, including
compiler-generated public constants. It saved each full Lean `Expr` type,
ordered universe parameters, declaration kind and transitive axiom closure.
Post-migration inspection in `a5b97448-8a04-436c-8266-d6a2dee1089d` found
the exact same 307 names, kinds, ordered universes and axiom sets.

Moving a module changes the module component of Lean's generated hygienic
bound-variable names. Accordingly, raw `reprStr` values differ for 163 types.
Check `013ef94f-5257-490f-be09-d5c2bbccf534` embeds all 307 saved baseline
expressions as `Lean.Expr` data and compares each with the migrated complete
type using `Expr.equal` after recursively erasing only names in `forallE`,
`lam` and `letE` binders. **All 307 comparisons pass.** Binder annotations,
parameter order, independent universe levels, instances, constants, metadata,
projections and every other expression node remain part of the comparison.
This is complete type preservation up to bound-variable renaming, not a test
of selected applications. No private constant rename is needed in these types.
The original proof bodies are also covered by the byte comparison above.

The union of the inspected axiom closures is exactly `propext`,
`Classical.choice` and `Quot.sound`, both before and after the migration.
No project axiom, `sorry`, `admit` or proof hole is introduced. The inspection
code is private verification tooling and is absent from the submitted Library.

Fresh closing-statement inspections returned `statement_returns_prop = true`,
with the same target fingerprints recorded for the prior statements:

| Closing declaration | Universe parameters | Target SHA-256 | New check |
| --- | --- | --- | --- |
| `Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement` | `u` | `1b87b27a4f2f760c082b607704102bc51f8d2f681ea577fa7db6d5ad8823239c` | `a5b97448-8a04-436c-8266-d6a2dee1089d` |
| `Langlands.LocalFactor.EulerFactorStructureStatement` | `u, v, w, z, t` | `dd0ab470f66a207bf6df629749c49c8249e1a4c78950174bbcb47341ef1f2468` | `013ef94f-5257-490f-be09-d5c2bbccf534` |
| `Langlands.LocalFactor.ArchimedeanAbelianLocalAnalysisStatement` | none | `dacc90e9f84bfdc175830bb4f55f7dfaacdceb8dc90b2b5a1bb48e644a292328` | `e16ea7ea-a5a1-44c1-a5f6-0d88989afd32` |
| `Langlands.LocalFactors.PadicHarmonicAnalysisStatement` | `u` | `96cb5af71f21e075cad111e69a8f9db3c6af1a2f97c23eefe3408ed892da277e` | `c99a391b-6295-4637-8774-4bfad8a51983` |

The complete public declaration map is the identity on the following inventory.
Entries are grouped by their old owning module; compiler-generated constants
are included to make the preservation boundary explicit.

<details>
<summary>Langlands.LocalFactor.Abelian: 32 unchanged public names</summary>

```text
Langlands.HarmonicAnalysis.Quasicharacter.continuousOn_epsilonIntegrand
Langlands.HarmonicAnalysis.Quasicharacter.continuousOn_extendZero
Langlands.HarmonicAnalysis.Quasicharacter.epsilonIntegrand
Langlands.HarmonicAnalysis.Quasicharacter.extendZero
Langlands.HarmonicAnalysis.Quasicharacter.extendZero.eq_1
Langlands.HarmonicAnalysis.Quasicharacter.extendZero_ne_zero
Langlands.HarmonicAnalysis.Quasicharacter.extendZero_unit
Langlands.HarmonicAnalysis.Quasicharacter.extendZero_zero
Langlands.PadicField.TopologicalData.abelianEpsilonExpression
Langlands.PadicField.TopologicalData.abelianEpsilonExpression.eq_1
Langlands.PadicField.TopologicalData.abelianEpsilonExpression_ramified
Langlands.PadicField.TopologicalData.abelianEpsilonExpression_unramified
Langlands.PadicField.TopologicalData.abelianEpsilonExpression_unramified_scale
Langlands.PadicField.TopologicalData.abelianGaussIntegral
Langlands.PadicField.TopologicalData.abelianScale
Langlands.PadicField.TopologicalData.abelianScale_abs_pos
Langlands.PadicField.TopologicalData.abelianScale_order
Langlands.PadicField.TopologicalData.abelianScale_value
Langlands.PadicField.TopologicalData.epsilonIntegrand_integrable
Langlands.PadicField.TopologicalData.epsilonShell
Langlands.PadicField.TopologicalData.integerVolume
Langlands.PadicField.TopologicalData.integerVolume_measure_ne_top
Langlands.PadicField.TopologicalData.mem_valuationShell_iff_scaled_integral_unit
Langlands.PadicField.TopologicalData.normalizedAbs.eq_1
Langlands.PadicField.TopologicalData.normalizedAbs_unit_eq_of_value_eq
Langlands.PadicField.TopologicalData.ord.eq_1
Langlands.PadicField.TopologicalData.unramified_value_eq_of_value_eq
Langlands.PadicField.TopologicalData.valuationShell
Langlands.PadicField.TopologicalData.valuationShell._proof_1
Langlands.PadicField.TopologicalData.valuationShell.eq_1
Langlands.PadicField.TopologicalData.valuationShell_compact_closed
Langlands.PadicField.TopologicalData.valuationShell_ne_zero
```

</details>

<details>
<summary>Langlands.LocalFactor.PadicAbelian: 79 unchanged public names</summary>

```text
Langlands.LocalFactor.PadicAbelian.AdditiveConductorAt
Langlands.LocalFactor.PadicAbelian.BorelMeasure
Langlands.LocalFactor.PadicAbelian.ConductorAt
Langlands.LocalFactor.PadicAbelian.ConvergesAt
Langlands.LocalFactor.PadicAbelian.ExtendsIntegral
Langlands.LocalFactor.PadicAbelian.RegularPoint
Langlands.LocalFactor.PadicAbelian.RegularPoint.eq_1
Langlands.LocalFactor.PadicAbelian.SelfDualHaar
Langlands.LocalFactor.PadicAbelian.SelfDualHaar._proof_1
Langlands.LocalFactor.PadicAbelian.SelfDualHaar._proof_2
Langlands.LocalFactor.PadicAbelian.SelfDualHaar._proof_3
Langlands.LocalFactor.PadicAbelian.SelfDualHaar._proof_4
Langlands.LocalFactor.PadicAbelian.SelfDualHaar._proof_5
Langlands.LocalFactor.PadicAbelian.additiveConductorAt_iff
Langlands.LocalFactor.PadicAbelian.centeredConstant
Langlands.LocalFactor.PadicAbelian.centeredConstant._proof_1
Langlands.LocalFactor.PadicAbelian.characterExtension
Langlands.LocalFactor.PadicAbelian.characterExtension_eq_extendZero
Langlands.LocalFactor.PadicAbelian.coe_regularLValue
Langlands.LocalFactor.PadicAbelian.conductorAt_iff
Langlands.LocalFactor.PadicAbelian.conductorAt_iff._simp_1_1
Langlands.LocalFactor.PadicAbelian.deligneConstant
Langlands.LocalFactor.PadicAbelian.deligneConstant.eq_1
Langlands.LocalFactor.PadicAbelian.deligneConstant_eq_abelianEpsilonExpression
Langlands.LocalFactor.PadicAbelian.epsilon
Langlands.LocalFactor.PadicAbelian.epsilon.eq_1
Langlands.LocalFactor.PadicAbelian.epsilonAt
Langlands.LocalFactor.PadicAbelian.epsilonAt.eq_1
Langlands.LocalFactor.PadicAbelian.gaussIntegrand
Langlands.LocalFactor.PadicAbelian.gaussIntegrand.eq_1
Langlands.LocalFactor.PadicAbelian.gaussIntegrand_integrable
Langlands.LocalFactor.PadicAbelian.gaussIntegrand_on_shell
Langlands.LocalFactor.PadicAbelian.gaussIntegrand_zero
Langlands.LocalFactor.PadicAbelian.gaussShell
Langlands.LocalFactor.PadicAbelian.gaussShell_eq_valuationShell
Langlands.LocalFactor.PadicAbelian.gaussShell_eq_valuationShell._simp_1_1
Langlands.LocalFactor.PadicAbelian.integerRing
Langlands.LocalFactor.PadicAbelian.integerRing.eq_1
Langlands.LocalFactor.PadicAbelian.integerRing_eq
Langlands.LocalFactor.PadicAbelian.integralUnits
Langlands.LocalFactor.PadicAbelian.lFactor
Langlands.LocalFactor.PadicAbelian.lFactor.eq_1
Langlands.LocalFactor.PadicAbelian.lFactorAt
Langlands.LocalFactor.PadicAbelian.lFactorAt.eq_1
Langlands.LocalFactor.PadicAbelian.lPolynomial
Langlands.LocalFactor.PadicAbelian.lPolynomial.eq_1
Langlands.LocalFactor.PadicAbelian.lPolynomial_coeff_zero
Langlands.LocalFactor.PadicAbelian.lPolynomial_ne_zero
Langlands.LocalFactor.PadicAbelian.langlandsConstantAtSelfDual
Langlands.LocalFactor.PadicAbelian.langlandsEpsilonAtSelfDual
Langlands.LocalFactor.PadicAbelian.langlandsEpsilonAtSelfDual_half
Langlands.LocalFactor.PadicAbelian.laurentEvaluation
Langlands.LocalFactor.PadicAbelian.normalizedAbs_on_gaussShell
Langlands.LocalFactor.PadicAbelian.rationalLFactor
Langlands.LocalFactor.PadicAbelian.rationalLFactor._proof_1
Langlands.LocalFactor.PadicAbelian.rationalLFactor_mul_denominator
Langlands.LocalFactor.PadicAbelian.rationalLFactor_ne_zero
Langlands.LocalFactor.PadicAbelian.regularLValue
Langlands.LocalFactor.PadicAbelian.regularLValue._proof_1
Langlands.LocalFactor.PadicAbelian.regularPoint_iff_polynomial_ne_zero
Langlands.LocalFactor.PadicAbelian.spectralVariable
Langlands.LocalFactor.PadicAbelian.uniformizerUnit
Langlands.LocalFactor.PadicAbelian.uniformizerUnit._proof_1
Langlands.LocalFactor.PadicAbelian.uniformizerUnit.eq_1
Langlands.LocalFactor.PadicAbelian.uniformizerUnit_coe
Langlands.LocalFactor.PadicAbelian.uniformizerUnit_ord
Langlands.LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs
Langlands.LocalFactor.PadicAbelian.uniformizerUnit_zpow_value
Langlands.LocalFactor.PadicAbelian.uniformizerUnit_zpow_value._simp_1_2
Langlands.LocalFactor.PadicAbelian.unitLevel
Langlands.LocalFactor.PadicAbelian.unitLevel._proof_1
Langlands.LocalFactor.PadicAbelian.unitLevel.eq_1
Langlands.LocalFactor.PadicAbelian.unitLevel_iff_mem_principalUnits
Langlands.LocalFactor.PadicAbelian.unitLevel_iff_mem_principalUnits._proof_1_2
Langlands.LocalFactor.PadicAbelian.zeta
Langlands.LocalFactor.PadicAbelian.zetaIntegrand
Langlands.PadicField.TopologicalData.abelianGaussIntegral.eq_1
Langlands.PadicField.TopologicalData.epsilonShell.eq_1
Langlands.PadicField.TopologicalData.integerVolume.eq_1
```

</details>

<details>
<summary>Langlands.LocalFactor.ReciprocalEntire: 58 unchanged public names</summary>

```text
Langlands.LocalFactor.ReciprocalEntire
Langlands.LocalFactor.ReciprocalEntire.IsPole
Langlands.LocalFactor.ReciprocalEntire.IsPole.eq_1
Langlands.LocalFactor.ReciprocalEntire.RegularPoint
Langlands.LocalFactor.ReciprocalEntire._sizeOf_1
Langlands.LocalFactor.ReciprocalEntire._sizeOf_inst
Langlands.LocalFactor.ReciprocalEntire.casesOn
Langlands.LocalFactor.ReciprocalEntire.coe_eval
Langlands.LocalFactor.ReciprocalEntire.ctorIdx
Langlands.LocalFactor.ReciprocalEntire.denominator
Langlands.LocalFactor.ReciprocalEntire.denominator_eventually_ne_zero
Langlands.LocalFactor.ReciprocalEntire.denominator_mul
Langlands.LocalFactor.ReciprocalEntire.denominator_product
Langlands.LocalFactor.ReciprocalEntire.denominator_shift
Langlands.LocalFactor.ReciprocalEntire.entire
Langlands.LocalFactor.ReciprocalEntire.eval
Langlands.LocalFactor.ReciprocalEntire.eval._proof_1
Langlands.LocalFactor.ReciprocalEntire.ext
Langlands.LocalFactor.ReciprocalEntire.ext_iff
Langlands.LocalFactor.ReciprocalEntire.germ
Langlands.LocalFactor.ReciprocalEntire.germ_meromorphic
Langlands.LocalFactor.ReciprocalEntire.germ_mul
Langlands.LocalFactor.ReciprocalEntire.isPole_iff_no_analytic_germ
Langlands.LocalFactor.ReciprocalEntire.isPole_iff_no_analytic_germ.match_1_1
Langlands.LocalFactor.ReciprocalEntire.isPole_mul
Langlands.LocalFactor.ReciprocalEntire.isPole_product
Langlands.LocalFactor.ReciprocalEntire.isPole_product._simp_1_7
Langlands.LocalFactor.ReciprocalEntire.mk
Langlands.LocalFactor.ReciprocalEntire.mk._flat_ctor
Langlands.LocalFactor.ReciprocalEntire.mk.congr_simp
Langlands.LocalFactor.ReciprocalEntire.mk.inj
Langlands.LocalFactor.ReciprocalEntire.mk.injEq
Langlands.LocalFactor.ReciprocalEntire.mk.noConfusion
Langlands.LocalFactor.ReciprocalEntire.mk.sizeOf_spec
Langlands.LocalFactor.ReciprocalEntire.mul
Langlands.LocalFactor.ReciprocalEntire.mul._proof_1
Langlands.LocalFactor.ReciprocalEntire.mul._proof_2
Langlands.LocalFactor.ReciprocalEntire.noConfusion
Langlands.LocalFactor.ReciprocalEntire.noConfusionType
Langlands.LocalFactor.ReciprocalEntire.nonzero
Langlands.LocalFactor.ReciprocalEntire.one
Langlands.LocalFactor.ReciprocalEntire.one._proof_1
Langlands.LocalFactor.ReciprocalEntire.one._proof_2
Langlands.LocalFactor.ReciprocalEntire.one.eq_1
Langlands.LocalFactor.ReciprocalEntire.product
Langlands.LocalFactor.ReciprocalEntire.product._f
Langlands.LocalFactor.ReciprocalEntire.product._sunfold
Langlands.LocalFactor.ReciprocalEntire.product._unsafe_rec
Langlands.LocalFactor.ReciprocalEntire.product.eq_1
Langlands.LocalFactor.ReciprocalEntire.product.eq_2
Langlands.LocalFactor.ReciprocalEntire.product.eq_def
Langlands.LocalFactor.ReciprocalEntire.product.match_1
Langlands.LocalFactor.ReciprocalEntire.product_perm
Langlands.LocalFactor.ReciprocalEntire.rec
Langlands.LocalFactor.ReciprocalEntire.recOn
Langlands.LocalFactor.ReciprocalEntire.shift
Langlands.LocalFactor.ReciprocalEntire.shift._proof_1
Langlands.LocalFactor.ReciprocalEntire.shift._proof_2
```

</details>

<details>
<summary>Langlands.LocalFactor.Archimedean: 54 unchanged public names</summary>

```text
Langlands.LocalFactor.Archimedean.GammaBlock
Langlands.LocalFactor.Archimedean.GammaBlock._sizeOf_1
Langlands.LocalFactor.Archimedean.GammaBlock._sizeOf_inst
Langlands.LocalFactor.Archimedean.GammaBlock.casesOn
Langlands.LocalFactor.Archimedean.GammaBlock.complex
Langlands.LocalFactor.Archimedean.GammaBlock.complex.elim
Langlands.LocalFactor.Archimedean.GammaBlock.complex.inj
Langlands.LocalFactor.Archimedean.GammaBlock.complex.injEq
Langlands.LocalFactor.Archimedean.GammaBlock.complex.noConfusion
Langlands.LocalFactor.Archimedean.GammaBlock.complex.sizeOf_spec
Langlands.LocalFactor.Archimedean.GammaBlock.complex_isPole
Langlands.LocalFactor.Archimedean.GammaBlock.ctorElim
Langlands.LocalFactor.Archimedean.GammaBlock.ctorElimType
Langlands.LocalFactor.Archimedean.GammaBlock.ctorIdx
Langlands.LocalFactor.Archimedean.GammaBlock.factor
Langlands.LocalFactor.Archimedean.GammaBlock.factor.match_1
Langlands.LocalFactor.Archimedean.GammaBlock.noConfusion
Langlands.LocalFactor.Archimedean.GammaBlock.noConfusionType
Langlands.LocalFactor.Archimedean.GammaBlock.real
Langlands.LocalFactor.Archimedean.GammaBlock.real.elim
Langlands.LocalFactor.Archimedean.GammaBlock.real.inj
Langlands.LocalFactor.Archimedean.GammaBlock.real.injEq
Langlands.LocalFactor.Archimedean.GammaBlock.real.noConfusion
Langlands.LocalFactor.Archimedean.GammaBlock.real.sizeOf_spec
Langlands.LocalFactor.Archimedean.GammaBlock.real_isPole
Langlands.LocalFactor.Archimedean.GammaBlock.rec
Langlands.LocalFactor.Archimedean.GammaBlock.recOn
Langlands.LocalFactor.Archimedean.complexTateEpsilon
Langlands.LocalFactor.Archimedean.complexTateEpsilon_ne_zero
Langlands.LocalFactor.Archimedean.complexTateL
Langlands.LocalFactor.Archimedean.gammaComplex
Langlands.LocalFactor.Archimedean.gammaComplex._proof_1
Langlands.LocalFactor.Archimedean.gammaComplex._simp_1
Langlands.LocalFactor.Archimedean.gammaComplex.eq_1
Langlands.LocalFactor.Archimedean.gammaComplex_eval
Langlands.LocalFactor.Archimedean.gammaComplex_isPole
Langlands.LocalFactor.Archimedean.gammaComplex_isPole._simp_1_2
Langlands.LocalFactor.Archimedean.gammaProduct
Langlands.LocalFactor.Archimedean.gammaProduct.eq_1
Langlands.LocalFactor.Archimedean.gammaProduct_isPole
Langlands.LocalFactor.Archimedean.gammaProduct_isPole._simp_1_2
Langlands.LocalFactor.Archimedean.gammaProduct_isPole._simp_1_3
Langlands.LocalFactor.Archimedean.gammaProduct_perm
Langlands.LocalFactor.Archimedean.gammaReal
Langlands.LocalFactor.Archimedean.gammaReal._proof_1
Langlands.LocalFactor.Archimedean.gammaReal.eq_1
Langlands.LocalFactor.Archimedean.gammaReal_eval
Langlands.LocalFactor.Archimedean.gammaReal_isPole
Langlands.LocalFactor.Archimedean.gammaReal_isPole._simp_1_2
Langlands.LocalFactor.Archimedean.gammaReal_isPole._simp_1_3
Langlands.LocalFactor.Archimedean.realTateEpsilon
Langlands.LocalFactor.Archimedean.realTateEpsilon_ne_zero
Langlands.LocalFactor.Archimedean.realTateL
Langlands.LocalFactor.ReciprocalEntire.eval.eq_1
```

</details>

<details>
<summary>Langlands.LocalFactor.ArchimedeanStatement: 9 unchanged public names</summary>

```text
Langlands.LocalFactor.ArchimedeanAbelianLocalAnalysisStatement
Langlands.LocalFactor.ArchimedeanQuasicharactersStatement
Langlands.LocalFactor.ArchimedeanQuasicharactersStatement._proof_1
Langlands.LocalFactor.ComplexArchimedeanFourierStatement
Langlands.LocalFactor.ComplexArchimedeanFourierStatement._proof_1
Langlands.LocalFactor.ComplexArchimedeanTateStatement
Langlands.LocalFactor.RealArchimedeanFourierStatement
Langlands.LocalFactor.RealArchimedeanFourierStatement._proof_1
Langlands.LocalFactor.RealArchimedeanTateStatement
```

</details>

<details>
<summary>Langlands.LocalFactor.Euler: 32 unchanged public names</summary>

```text
Langlands.LocalFactor.RegularPoint
Langlands.LocalFactor.SpectralRegularPoint
Langlands.LocalFactor.SpectralRegularPoint._proof_1
Langlands.LocalFactor.coe_regularFactorValue
Langlands.LocalFactor.eulerPolynomial
Langlands.LocalFactor.eulerPolynomial.congr_simp
Langlands.LocalFactor.eulerPolynomial.eq_1
Langlands.LocalFactor.eulerPolynomial_coeff_zero
Langlands.LocalFactor.eulerPolynomial_conj
Langlands.LocalFactor.eulerPolynomial_eq_det
Langlands.LocalFactor.eulerPolynomial_eval
Langlands.LocalFactor.eulerPolynomial_eval_zero
Langlands.LocalFactor.eulerPolynomial_ne_zero
Langlands.LocalFactor.rationalFactor
Langlands.LocalFactor.rationalFactor._proof_1
Langlands.LocalFactor.rationalFactor._proof_2
Langlands.LocalFactor.rationalFactor.eq_1
Langlands.LocalFactor.rationalFactor_conj
Langlands.LocalFactor.rationalFactor_mul_eulerPolynomial
Langlands.LocalFactor.rationalFactor_ne_zero
Langlands.LocalFactor.regularFactorValue
Langlands.LocalFactor.regularFactorValue._proof_1
Langlands.LocalFactor.regularFactorValue_det
Langlands.LocalFactor.regularFactorValue_zero
Langlands.LocalFactor.spectralFactorValue
Langlands.LocalFactor.spectralFactorValue._proof_1
Langlands.LocalFactor.spectralFactorValue_det
Langlands.LocalFactor.spectralParameter
Langlands.LocalFactor.spectralParameter._proof_1
Langlands.LocalFactor.spectralParameter_eq_cpow
Langlands.LocalFactor.zeroRegularPoint
Langlands.LocalFactor.zeroRegularPoint._proof_1
```

</details>

<details>
<summary>Langlands.LocalFactor.EulerStatement: 25 unchanged public names</summary>

```text
Langlands.LocalFactor.EulerCyclicBlockStatement
Langlands.LocalFactor.EulerCyclicBlockStatement._proof_1
Langlands.LocalFactor.EulerCyclicBlockStatement._proof_2
Langlands.LocalFactor.EulerCyclicBlockStatement._proof_3
Langlands.LocalFactor.EulerCyclicBlockStatement._proof_4
Langlands.LocalFactor.EulerDirectSumStatement
Langlands.LocalFactor.EulerDirectSumStatement._proof_1
Langlands.LocalFactor.EulerDirectSumStatement._proof_2
Langlands.LocalFactor.EulerDirectSumStatement._proof_3
Langlands.LocalFactor.EulerExactSequenceStatement
Langlands.LocalFactor.EulerExactSequenceStatement._proof_1
Langlands.LocalFactor.EulerExactSequenceStatement._proof_2
Langlands.LocalFactor.EulerExactSequenceStatement._proof_3
Langlands.LocalFactor.EulerFactorStructureStatement
Langlands.LocalFactor.EulerScalarAndReciprocalStatement
Langlands.LocalFactor.EulerScalarAndReciprocalStatement._proof_1
Langlands.LocalFactor.EulerScalarAndReciprocalStatement._proof_2
Langlands.LocalFactor.EulerSpectralTranslationStatement
Langlands.LocalFactor.EulerSpectralTranslationStatement._proof_1
Langlands.LocalFactor.EulerSpectralTranslationStatement._proof_2
Langlands.LocalFactor.EulerTensorEigenbasisStatement
Langlands.LocalFactor.EulerTensorEigenbasisStatement._proof_1
Langlands.LocalFactor.EulerTensorEigenbasisStatement._proof_2
Langlands.LocalFactor.EulerTensorEigenbasisStatement._proof_3
Langlands.LocalFactor.EulerUnipotentInvarianceStatement
```

</details>

<details>
<summary>Langlands.LocalFactors.Harmonic.Statement: 12 unchanged public names</summary>

```text
Langlands.LocalFactors.PadicAdditiveConductorStatement
Langlands.LocalFactors.PadicFourierClosureStatement
Langlands.LocalFactors.PadicFourierDualityStatement
Langlands.LocalFactors.PadicFourierDualityStatement._proof_1
Langlands.LocalFactors.PadicFourierDualityStatement._proof_2
Langlands.LocalFactors.PadicFourierDualityStatement._proof_3
Langlands.LocalFactors.PadicFourierDualityStatement._proof_4
Langlands.LocalFactors.PadicFourierNormalizationStatement
Langlands.LocalFactors.PadicFourierNormalizationStatement._proof_1
Langlands.LocalFactors.PadicFourierScalingStatement
Langlands.LocalFactors.PadicFourierScalingStatement._proof_1
Langlands.LocalFactors.PadicHarmonicAnalysisStatement
```

</details>

<details>
<summary>Langlands.LocalFactor.PadicAbelianStatement: 6 unchanged public names</summary>

```text
Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement
Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement._proof_1
Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement._proof_2
Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement._proof_3
Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement._proof_4
Langlands.LocalFactor.PadicAbelianLocalAnalysisStatement._proof_5
```

</details>

### Whole-tree validation

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. A private umbrella imports
all 277 workspace Library modules, including the eight old-path wrappers.
Check `a5b97448-8a04-436c-8266-d6a2dee1089d` built this umbrella and
the declaration audit with incremental **Lake**: 280 jobs, exit code 0,
zero errors, zero warnings, no limited output and a quiet terminal process tree.
Its source snapshot SHA-256 is
`7a254728800f75b3f8fb402eff048a3236fb139fc12c7fe31b25a4ffd7b9dd3c`.
The complete-type and later closing-statement checks also terminated successfully.
Mathlib was neither downloaded nor rebuilt. The private umbrella and audit
modules are excluded from staging; the public snapshot contains 277 modules.
Compilation and preservation checks establish neither independent semantic
acceptance nor publication; both remain required by this task.

### Coordination and integration sequence

The sequence is: inspect the current base and importers; contact the original
authors and branch owners; record the baseline; create the canonical pairs and
old-path re-exports together; rewrite published importers and documentation;
compare complete declarations and build the whole tree; freeze one coherent
candidate; obtain independent review and integration; then release downstream
work to the published canonical paths.

Before edits, Worker 33 explicitly agreed to the three statement moves and
`PadicAbelianStatement` import rewrite. Workers 20 and 4 reported no competing
edits. Worker 35 reported no global consumer. Worker 31 was contacted again
about JPSS; its prior coordination reported no consumer. Worker 40 confirmed
that its attachment uses the existing declarations and can consume the old-path
re-export. Worker 46 was contacted about rank-one stability and WD statements.
Worker 12 confirmed that regular-evaluation construction/adapters will freeze
only after this layout publishes. These messages authorize no edits to another
worker's frozen candidate or task objective.

Pending consumers at the coordination checkpoint are:

| Owner | Candidate or draft | Old import retained by compatibility |
| --- | --- | --- |
| Worker 33 | `fbebb012-2d2b-445f-a0f5-f8c6fe6cda6b`, `ArchimedeanPresentationStatement` | `Langlands.LocalFactor.Archimedean` |
| Worker 20 | `b15ea006-9fae-4d3d-8f20-9dd4d17fbb95`, `WeilDeligne` / `WeilDeligneConductor` | `Langlands.LocalFactor.Euler` |
| Worker 40 | `a30ca04d-f66e-49d4-86ce-590aa23b5114`, `ArchimedeanAttachment` | `Langlands.LocalFactor.Archimedean` |
| Workers 33 and 46 | `RankOneStabilityStatement` (reported candidate prefix `8d72ea08`) | `Langlands.LocalFactor.PadicAbelian` |
| Worker 46 | unstaged WD Euler/correction statements | `Langlands.LocalFactor.Euler` |

The first three import lists were inspected directly in the frozen snapshots.
A validation-only notice for rank-one stability was explicitly corrected by
Worker 33; it is not evidence of acceptance or publication. None of these
pending candidates is replaced or changed by this submission. The old paths
remain usable throughout the integration window. Newly published consumers
must have their actual imports and documentation reconciled with the canonical
paths during integration or a follow-up within this structural task.

A final scan of current Library `fc2adf231e015f979345e06d0d80283856c43c7f`
found no newly published affected importer or documentation reference since
the recorded base. The Integrator must validate its actual merged tree;
this record does not claim that concurrent unpublished work was validated.

At integration against Library `68e8013fc4fed0de284fd849695676aca2e0c32d`,
the combined tree includes `ArchimedeanPresentationStatement`,
`RankOneStabilityStatement`, `ArchimedeanAttachment`, and `WeilDeligne`.
Their imports and paired dependency descriptions now use the canonical paths.
The old-path compatibility modules remain available. The coordination table
above records the earlier checkpoint, not the status of these integrated files.
