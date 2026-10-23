# FML exact conductor predicates and supplied local-field instances

Import `Langlands.LocalFactor.FML.Conductors` for this interface together with
the [valuation and filtration definitions](Valuation.md) and
[character types and transport](Characters.md). The generic definitions live
in `Langlands.FML`, with arbitrary `F : Type u` and hypotheses
`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`.

## Exact conductor predicates

`AddCharTrivialOnLattice F ψ r` means that the continuous additive character
`ψ` takes value `1` on every element of `lattice F r`.
`QuasiCharTrivialOnUnitFiltration F χ m` means that `χ` takes value `1` on
every element of `unitFiltration F m`. These predicates describe triviality
on entire sets, not equality of those sets with a pointwise character kernel.

`IsAdditiveConductor F ψ n`, with `n : ℤ`, is the conjunction of

1. `AddCharTrivialOnLattice F ψ (-n)`;
2. for every `r : ℤ`, `AddCharTrivialOnLattice F ψ r → -n ≤ r`.

Thus the least triviality depth is **`-n`**. The sign is part of the definition.
`IsMultiplicativeConductor F χ m`, with `m : ℕ`, is the conjunction of

1. `QuasiCharTrivialOnUnitFiltration F χ m`;
2. for every `r : ℕ`, `QuasiCharTrivialOnUnitFiltration F χ r → m ≤ r`.

Conductor zero here means triviality on the integral units `U⁰`; it does not
assert that the quasicharacter is globally trivial.
Both conductor predicates are `Prop`-valued definitions. Their triviality and
minimality components are accessed by `.1` and `.2`.

`LocalAddCharData F` packages `character : ContinuousAddChar F`,
`conductor : ℤ`, and `isConductor : IsAdditiveConductor F character conductor`.
`LocalQuasiCharData F` packages `character : ContinuousQuasiChar F`,
`conductor : ℕ`, and the analogous multiplicative certificate. These
structures require supplied certificates; this module proves no existence
theorem and makes no canonical conductor choice. In particular,
`LocalAddCharData` has exactly these three fields, with no additional explicit
nontriviality field. Nontriviality of transported Library characters is proved
in `Characters.lean`.

## Explicit specialization to the Library's p-adic fields

Take `{p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}` and
`T : F.TopologicalData`. The namespace `Langlands.FML.Padic` exposes:

| Name, with explicit first argument `T` | Result |
| --- | --- |
| `normalizedValuation T` | `Valuation F.Carrier ℤᵐ⁰` |
| `ord T` | `AddValuation F.Carrier (WithTop ℤ)` |
| `lattice T n` | `Submodule T.Integers F.Carrier` for `n : ℤ` |
| `unitFiltration T n` | `Subgroup F.Carrierˣ` for `n : ℕ` |
| `ofUnitaryAdditiveCharacter T ψ` | `ContinuousAddChar F.Carrier`, with topology exactly `T.topology` |

The first four abbreviations install `T.topology`, `T.valuativeRel` and
`T.localField` with local `letI` bindings, and then invoke the generic FML
definitions. The underlying field instance is the one on `F.Carrier`.
The character abbreviation uses `T.topology` explicitly in both its input and
output types. The scalar ring in `lattice T n` is definitionally
`T.Integers`, from `Langlands.LocalField.Normalization.Definitions`.

`normalizedValuation_eq_discreteValuation T` proves
`normalizedValuation T = T.discreteValuation` by reflexivity: both use the
same canonical value-group equivalence. This pins the valuation intended for
subsequent agreement statements.

For a generic conductor predicate on this supplied field, install the same
three local instances and use `Langlands.FML.IsAdditiveConductor F.Carrier`
or `Langlands.FML.IsMultiplicativeConductor F.Carrier`. A Library
quasicharacter already has the required type definitionally; the additive
character uses the transport above.

The FML additive order sends zero to `⊤`; the Library's integer-valued
`T.ord` has value `0` at zero. No equality of these whole functions is asserted.
Agreement of the lattice, unit-filtration and conductor conventions with the
Library interfaces is reserved for the subsequent statement and proof units.
No finite local constant or equality with a Library epsilon or self-dual
constant is constructed here.

## Source and modifications

Adapted by Worker 20 from Fukuhiro Ueda, *epsilon_FML*, commit
`0b4159be50e1bd45ddff1de4280399576a3e2024`, Apache-2.0; see the retained,
unchanged [LICENSE](LICENSE). The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Within `fukubillueda-web--epsilon_FML/source/LanglandsFirstMainLemma/`,
`Basic/CharacterConductors.lean` supplies:

- lines 30–36: the two whole-set triviality predicates;
- lines 90–102: the sign and minimality conventions and exact conductor data;
- lines 394–405: the two character-and-conductor packages.

That original file's SHA-256 is
`8e1bfb06c5aa64800f78e8e73b3882748832618ea33cfdc8f8161d1687f5a2ec`.
The supporting source locations and file fingerprints are recorded in
`Valuation.md` and `Characters.md`.

The port changes the namespace and imports, makes the universe explicit, and
replaces the upstream two-field `Prop` structures for exact conductors by
conjunction-valued `def`s with the same mathematical content. It retains only
the predicates and data packages from that upstream module. The `Padic`
abbreviations and reflexive valuation identification are new internal
integration definitions and a supporting proof, derived from the current
Library `PadicField.TopologicalData` and its normalization definitions.
The original repository has no `NOTICE` file or Lean copyright headers;
the adaptation notices identify the original author and these modifications.
