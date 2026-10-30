# FML and Library conductor agreement statements

Import `Langlands.LocalFactor.FML.AgreementStatement`. This module defines four
independent propositions in `Langlands.FML.Padic`. Each declaration has type
`Prop`, is polymorphic in the arbitrary universe `u`, and internally quantifies
over `{p : ℕ}`, `[Fact p.Prime]`, `F : Langlands.PadicField.{u} p`, and
`T : F.TopologicalData`.

These are statement targets. This module supplies no proof of an agreement and
does not choose conductors or construct certified character packages. The
published proofs and packages that do are listed in
[Published proofs and packages](#published-proofs-and-packages).

## Exact targets and hypotheses

Each statement installs `T.topology`, `T.valuativeRel`, and `T.localField` with
local `letI` bindings before invoking the generic published FML definitions.
The field instance is the one on `F.Carrier`. No independent topology,
valuation, filtration, conductor, or comparison hypothesis is supplied.
The already published `FML.Padic` abbreviations install these same instances;
the statements use the underlying generic definitions explicitly.

| Declaration after `Langlands.FML.Padic.` | Quantification after `F` and `T` | Asserted agreement |
| --- | --- | --- |
| `LatticeAgreementStatement` | Every `n : ℤ` | `(FML.lattice F.Carrier (-n) : Set F.Carrier) = (T.additiveLattice n : Set F.Carrier)` |
| `UnitFiltrationAgreementStatement` | Every `k : ℕ` | `FML.unitFiltration F.Carrier k = T.principalUnits k` |
| `AdditiveConductorAgreementStatement` | Every `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier` and `n : ℤ` | `FML.IsAdditiveConductor F.Carrier (FML.ofUnitaryAdditiveCharacter ψ) n ↔ n = T.additiveConductor ψ` |
| `MultiplicativeConductorAgreementStatement` | Every `χ : HarmonicAnalysis.Quasicharacter F.Carrier` and `m : ℕ` | `FML.IsMultiplicativeConductor F.Carrier χ m ↔ m = T.multiplicativeConductor χ` |

Here `FML` abbreviates the namespace `Langlands.FML`, not a newly supplied
interface. The additive input is the actual Library structure containing a
continuous circle-valued additive character and its nontriviality certificate.
Its transported value at `x` is `Circle.toUnits (ψ x)`, by the published
`FML.ofUnitaryAdditiveCharacter_apply`. The published injectivity and
`FML.ofUnitaryAdditiveCharacter_ne_one` preserve its nontriviality. The same
topology `T.topology` governs both character types and the Library conductor.
The multiplicative input is the Library continuous homomorphism
`F.Carrierˣ →ₜ* ℂˣ`; it is definitionally the FML quasicharacter type.
It need not be unitary or nontrivial.

## Normalization and source-to-Library translation

The FML definitions are imported from
`Langlands.LocalFactor.FML.Conductors`, and the Library definitions from
`Langlands.HarmonicAnalysis.Conductor`. Both sides use the actual normalized
multiplicative valuation obtained by mapping `ValuativeRel.valuation` through
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`.
The published `FML.Padic.normalizedValuation_eq_discreteValuation T` identifies
that specialization with `T.discreteValuation` by reflexivity.

FML's additive valuation has value `⊤` at zero and negative logarithm of that
multiplicative valuation otherwise. Its lattice at depth `r` consists of
elements of additive order at least `r`. The Library's `T.additiveLattice n`
consists of elements with `T.discreteValuation x ≤ WithZero.exp n` and represents
`π^(-n) O`. The first target therefore uses **depth `-n`**, for all integers.
It compares underlying sets: FML packages a submodule over the integer ring,
whereas the Library packages an additive subgroup.
The Library's integer-valued `T.ord` takes value zero at zero; the target does
not identify it with the FML `WithTop ℤ`-valued function.

FML's zeroth unit layer is the canonical valuation-ring unit subgroup.
At a positive depth `k` it also requires additive order of `u - 1` at least
`k`. The Library's `T.principalUnits k` requires normalized valuation of `u`
equal to one and normalized valuation of `u - 1` at most
`WithZero.exp (-(k : ℤ))`. At zero the second condition is redundant, as the
published `T.mem_principalUnits_zero` states. The second target retains the
zero case and the natural-number indexing.

`FML.IsAdditiveConductor` requires triviality on the whole lattice at depth
`-n` and minimality of that depth among all integer triviality depths. In the
Library this corresponds to the greatest integer level with
`T.AdditiveTrivialAt ψ n`. The third target compares this exact predicate with
the already constructed `T.additiveConductor ψ`; its equality is oriented
`n = T.additiveConductor ψ`.
`FML.IsMultiplicativeConductor` requires triviality on the whole unit subgroup
at depth `m` and minimality among natural-number depths. The fourth target
compares it with the already constructed `T.multiplicativeConductor χ`,
with equality `m = T.multiplicativeConductor χ`.
Neither predicate identifies an entire character kernel.

The Library's existing specifications are `additiveConductor_spec`,
`additiveTrivialAt_iff_le_conductor`, `multiplicativeConductor_spec`, and
`multiplicativeTrivialAt_iff_conductor_le`, in
`Langlands.PadicField.TopologicalData`. They motivate the conductor comparisons.

## Published proofs and packages

All four targets are proved, outside this module, in
`Langlands.LocalFactor.FML.AgreementProof`, at the same arbitrary universe
`u`:

| Theorem after `Langlands.FML.Padic.` | Proves |
| --- | --- |
| `latticeAgreement` | `LatticeAgreementStatement.{u}` |
| `unitFiltrationAgreement` | `UnitFiltrationAgreementStatement.{u}`, every `k : ℕ`, including the zero layer |
| `additiveConductorAgreement` | `AdditiveConductorAgreementStatement.{u}` |
| `multiplicativeConductorAgreement` | `MultiplicativeConductorAgreementStatement.{u}` |

The canonical FML packages are constructed in
`Langlands.LocalFactor.FML.CanonicalPackages`.
`localQuasiCharData T χ` packages a Library quasicharacter with its existing
conductor `T.multiplicativeConductor χ`, certified by
`multiplicativeConductorAgreement`. `localAddCharData T ψ` packages the
transported character `FML.ofUnitaryAdditiveCharacter ψ` with
`T.additiveConductor ψ`, certified by `additiveConductorAgreement`.
Neither construction chooses a new conductor.

## Provenance and modifications

Worker 40 formulated these derived comparison targets between published
definitions. They are new Library integration statements, not theorems quoted
from the upstream repository. The FML definitions were adapted from Fukuhiro
Ueda, *epsilon_FML*, commit
`0b4159be50e1bd45ddff1de4280399576a3e2024`, Apache-2.0. The original unchanged
[LICENSE](LICENSE) and the attribution/modification notices in
[Valuation.md](Valuation.md), [Characters.md](Characters.md), and
[Conductors.md](Conductors.md) remain in this directory.

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Under `fukubillueda-web--epsilon_FML/source/LanglandsFirstMainLemma/`,
the precise original locations are:

- `LocalField/Valuation.lean:20–32,85–105`: normalized multiplicative valuation
  and additive order;
- `LocalField/Lattices.lean:67–88`: the integer ring, lattice and its membership;
- `LocalField/UnitFiltration.lean:19–24,67–104`: integral units and the natural
  unit filtration, including its separate zero case;
- `Basic/CharacterTypes.lean:20–26`: continuous additive and multiplicative
  character types;
- `Basic/CharacterConductors.lean:28–36,90–102`: whole-set triviality and the
  exact additive and multiplicative conductor conventions.

The corresponding Library definitions are in
`LocalField/Definitions.lean:65–70`,
`LocalField/Normalization/Definitions.lean:86–106`,
`HarmonicAnalysis/Basic.lean:19–32`, and
`HarmonicAnalysis/Conductor.lean:48–58,141–163,173–204,268–285`
(paths relative to `Langlands/`).
The translation adds the supplied p-adic field hypotheses, the explicit
circle-to-units character transport, and the four comparisons above.
It retains the original sign, zero unit layer, and exponent domains.
No conductor existence layer, finite local constant, First Main Lemma, or
epsilon/self-dual normalization comparison is added.
