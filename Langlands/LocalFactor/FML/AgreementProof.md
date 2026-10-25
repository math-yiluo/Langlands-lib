# FML and Library agreement proofs

Import `Langlands.LocalFactor.FML.AgreementProof`. This module proves the four
unchanged propositions in `Langlands.LocalFactor.FML.AgreementStatement`.
All names in the table are in `Langlands.FML.Padic`, and all four theorems have
the arbitrary universe parameter `u`.

| Theorem | Complete type |
| --- | --- |
| `latticeAgreement` | `LatticeAgreementStatement.{u}` |
| `unitFiltrationAgreement` | `UnitFiltrationAgreementStatement.{u}` |
| `additiveConductorAgreement` | `AdditiveConductorAgreementStatement.{u}` |
| `multiplicativeConductorAgreement` | `MultiplicativeConductorAgreementStatement.{u}` |

Each type retains the internal quantification over `{p : ℕ}`, `[Fact p.Prime]`,
`F : Langlands.PadicField.{u} p` and `T : F.TopologicalData`. The generic FML
objects use exactly `T.topology`, `T.valuativeRel` and `T.localField`. The
theorems add no hypotheses. In particular, they assume neither valuation
comparison nor conductor certificates. The additive statement quantifies over
the actual continuous, nontrivial circle-valued Library character and every
integer conductor candidate. The multiplicative statement quantifies over
every continuous Library quasicharacter and every natural conductor candidate;
unitarity and nontriviality are not required for that quasicharacter.

## Lattice and unit-filtration proof

`mem_lattice_iff_mem_additiveLattice T n x` compares FML lattice depth `-n`
with Library additive-lattice level `n`. It unfolds the FML order into the
conditional negative logarithm and applies the published
`normalizedValuation_eq_discreteValuation T`. Both normalizations map the
actual `ValuativeRel.valuation` through
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`.

At `x = 0`, the FML order is `⊤`, the multiplicative valuation is zero, and
both membership inequalities hold. For `x ≠ 0`, valuation nonvanishing allows
`WithZero.log_le_iff_le_exp`: the inequality
`-n ≤ -log (T.discreteValuation x)` is precisely
`T.discreteValuation x ≤ WithZero.exp n`. Set extensionality gives
`latticeAgreement`. The proof never identifies FML's infinite order at zero
with the Library's integer-valued `T.ord`, whose zero convention differs.

`mem_unitGroup_iff_discreteValuation_eq_one T x` first applies
`Valuation.mem_unitGroup_iff` to the canonical valuation subring.
The value-group isomorphism preserves one and is injective, so integral-unit
membership is equivalent to `T.discreteValuation (x : F.Carrier) = 1`.
For `unitFiltrationAgreement`, subgroup extensionality reduces equality to
membership. The natural index is split into zero and successor:

- At zero, `FML.unitFiltration_zero` and `T.mem_principalUnits_zero` reduce
  both sides to integral-unit membership. The Library's extra congruence
  inequality at zero is already redundant by the latter imported theorem.
- At `k + 1`, `FML.mem_unitFiltration_succ` retains the integral-unit condition
  and membership of `x - 1` in the lattice of depth `k + 1`. Applying the
  lattice comparison with level `-(k + 1)` gives exactly the Library bound
  `T.discreteValuation (x - 1) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ))`. This includes `x = 1`, since the lattice proof includes
  zero.

## Triviality and conductor proof

`addCharTrivialOnLattice_iff T ψ n` proves equivalence between FML triviality
at depth `-n` and `T.AdditiveTrivialAt ψ n`. Pointwise evaluation of the
transported character is the actual `Circle.toUnits (ψ x)`. Since
`Circle.toUnits` preserves one and is injective, this equals one exactly when
`ψ x = 1`. The lattice membership comparison then transports the universal
quantifier over the whole lattice.

For `additiveConductorAgreement`, the triviality component of an FML
certificate and `T.additiveTrivialAt_iff_le_conductor` give
`n ≤ T.additiveConductor ψ`. Its minimality component, tested at the negative
of the Library conductor and using `T.additiveConductor_spec`, gives the
reverse inequality after negation. Conversely, the Library specification
gives triviality at its conductor. For an arbitrary FML triviality depth
`r : ℤ`, the helper gives Library triviality at level `-r`; the existing
triviality criterion implies `-r ≤ T.additiveConductor ψ`, hence the required
`-T.additiveConductor ψ ≤ r`. Integer arithmetic closes these inequalities.
The resulting equality is oriented `n = T.additiveConductor ψ`.

`quasiCharTrivialOnUnitFiltration_iff T χ m` rewrites the actual subgroup
using `unitFiltrationAgreement`. There is no character transport: the
quasicharacter types are definitionally identical. For
`multiplicativeConductorAgreement`, FML minimality tested at the Library
conductor gives one inequality; FML triviality and
`T.multiplicativeTrivialAt_iff_conductor_le` give the other. The converse
uses `T.multiplicativeConductor_spec` and that same criterion. The index
remains natural, including zero, and equality is oriented
`m = T.multiplicativeConductor χ`. Neither triviality comparison asserts
equality of a lattice or subgroup with the entire character kernel.

## Dependencies, provenance and scope

Worker 96 implemented these new integration proofs following the comparison
route specified by Worker 332. Worker 40 authored the imported comparison
statements. Worker 20 authored the imported Library conductor constructions
and the FML definition adaptation. The direct valuation-isomorphism argument
also follows the pattern in the imported conductor module. Worker 332 and
Worker 20 are credited as contributors to the route and reused proof pattern.
No upstream agreement theorem is claimed: the four comparisons are derived
from the actual published Library definitions.

The original FML definitions are due to Fukuhiro Ueda, *epsilon_FML*, commit
`0b4159be50e1bd45ddff1de4280399576a3e2024`, Apache-2.0. Registered source:
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Within `fukubillueda-web--epsilon_FML/source/LanglandsFirstMainLemma/`,
the original locations checked for this comparison are:

- `LocalField/Valuation.lean:20–32,71–105`: the common normalization and
  negative-logarithm order, including infinity at zero;
- `LocalField/Lattices.lean:67–88`: the valuation ring and lattice carrier;
- `LocalField/UnitFiltration.lean:19–24,67–104`: integral units and the
  separate zero and positive unit layers;
- `Basic/CharacterTypes.lean:20–26`: continuous character types;
- `Basic/CharacterConductors.lean:28–36,90–102`: whole-set triviality and
  exact conductor extremality with the retained sign and index domains.

The current Library definitions and source translation are documented in
[AgreementStatement.md](AgreementStatement.md), [Valuation.md](Valuation.md),
[Characters.md](Characters.md), and [Conductors.md](Conductors.md).
Their files, modification notices and retained [Apache-2.0 license](LICENSE)
are unchanged. The source has no `NOTICE`; no applicable errata note was found
in the current Library or project notes. This new proof module changes no
upstream or imported declaration.

The sole direct import is `Langlands.LocalFactor.FML.AgreementStatement`.
Its existing dependency closure supplies
`Langlands.LocalFactor.FML.{Valuation,Characters,Conductors}`,
`Langlands.LocalField.Normalization.Definitions`,
`Langlands.HarmonicAnalysis.{Basic,Conductor}`, the actual field/topological
interface, and the pinned Mathlib valuation and order APIs.
The proofs use the Library's already proved conductor specifications; they
introduce no conductor existence or choice construction. Canonical FML
packages, finite local constants, epsilon comparisons, and both main lemmas
remain outside this module.

Each of the four theorems has its own proof record and exact target. A
validation receipt for one target does not validate the other three.
Development compilation is separate from independent semantic acceptance,
Lake/kernel and exact-target validation, and Library publication.
