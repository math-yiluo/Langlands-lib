# Canonical FML character packages using the Library conductors

Import `Langlands.LocalFactor.FML.CanonicalPackages`. The two definitions in
`Langlands.FML.Padic` package actual Library characters with the Library's
existing conductors and the published FML conductor agreement certificates.
They are derived integration definitions.

## Complete types and supplied instances

Both definitions have arbitrary universe parameter `u`, implicit
`{p : ℕ}`, `[Fact p.Prime]` and
`{F : Langlands.PadicField.{u} p}`, followed by the explicit argument
`T : F.TopologicalData`. Their complete types after these binders are:

```lean
localQuasiCharData
    (T : F.TopologicalData)
    (χ : @Langlands.HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Langlands.FML.LocalQuasiCharData F.Carrier

localAddCharData
    (T : F.TopologicalData)
    (ψ : @Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter
      F.Carrier _ T.topology) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Langlands.FML.LocalAddCharData F.Carrier
```

The field instance is `F.field`; the additive-group and monoid structures
are inherited from it. The character inputs explicitly use `T.topology`.
The output types and both definition bodies install exactly `T.topology`,
`T.valuativeRel` and `T.localField` with local `letI` bindings. Thus their
generic FML package types and conductor predicates use the same supplied
topology, valuative relation and nonarchimedean local-field certificate as the
agreement theorems. No additional topology or local-field instance is an
argument. `F` already carries its finite extension structure over `Padic p`;
`T` also carries the compatible valuative extension and module-topology
certificates required by the Library field interface.

## Exact formulas and certificates

With those same instances installed, the multiplicative package is

```lean
localQuasiCharData T χ =
  { character := χ
    conductor := T.multiplicativeConductor χ
    isConductor := (multiplicativeConductorAgreement F T χ _).mpr rfl }
```

The quasicharacter is the actual continuous homomorphism
`F.Carrierˣ →ₜ* ℂˣ`. It is definitionally the FML continuous quasicharacter;
there is no transport or restriction to unitary or nontrivial characters.
The natural-valued conductor includes zero. Its certificate states triviality
on the entire FML unit subgroup at that depth and minimality among all
natural-number triviality depths. At zero that subgroup is the integral
units `U⁰`; this condition does not require global triviality.

The additive package is

```lean
localAddCharData T ψ =
  { character := Langlands.FML.ofUnitaryAdditiveCharacter ψ
    conductor := T.additiveConductor ψ
    isConductor := (additiveConductorAgreement F T ψ _).mpr rfl }
```

Here `ψ` is the Library's continuous, nontrivial circle-valued additive
character. At every `x : F.Carrier`, the package character is exactly
`Circle.toUnits (ψ x)`, so its complex value is `(ψ x : ℂ)`.
The imported `ofUnitaryAdditiveCharacter` construction proves continuity into
the complex units. The imported `ofUnitaryAdditiveCharacter_ne_one` proves
nontriviality using the actual injective `Circle.toUnits`. The package stores
that transported continuous character, the integer conductor and the exact
conductor certificate; its structure has no separate nontriviality field.
The certificate gives triviality on the entire FML lattice at depth
`-T.additiveConductor ψ` and minimality of that integer depth. Equivalently,
the Library conductor is the greatest Library additive-lattice level of
triviality, using `lattice (-n) = additiveLattice n` on underlying sets.

Each certificate is obtained from the reverse direction of its published
agreement at the corresponding Library conductor. The equality required on
the right of the equivalence is reflexivity. In particular, the character
and conductor projections in these formulas are definitional equalities.
The definitions are `noncomputable` because they reuse the Library conductor
constructions; they introduce no new conductor existence proof, independently
chosen exponent, or choice layer.

## Dependencies and provenance

The sole direct import is
`Langlands.LocalFactor.FML.AgreementProof`. Its published closure supplies
the generic FML packages and character transport, the supplied p-adic field
and normalization interfaces, and `Langlands.HarmonicAnalysis.Conductor`.
The constructors use the accepted
`Langlands.FML.Padic.multiplicativeConductorAgreement` and
`Langlands.FML.Padic.additiveConductorAgreement` without changing any imported
statement, proof or definition. The lattice and unit-filtration comparisons
are dependencies of those agreement proofs.

Worker 455 implemented and documented these definitions from the formulas
specified by Worker 332. The imported adaptation is by Worker 20, the
comparison statements by Worker 40, and the agreement proofs by Worker 96.
Those published dependencies retain their own authorship and notices.

The upstream correspondence is Fukuhiro Ueda, *epsilon_FML*, commit
`0b4159be50e1bd45ddff1de4280399576a3e2024`,
[pinned repository](https://github.com/fukubillueda-web/epsilon_FML/tree/0b4159be50e1bd45ddff1de4280399576a3e2024),
Apache-2.0; see the retained unchanged [LICENSE](LICENSE).
The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Under `fukubillueda-web--epsilon_FML/source/LanglandsFirstMainLemma/`:

- `Basic/CharacterConductors.lean:390–405` defines the two package structures.
  File SHA-256:
  `8e1bfb06c5aa64800f78e8e73b3882748832618ea33cfdc8f8161d1687f5a2ec`.
- `Basic/CharacterConductorExistence.lean:284–347` defines independently
  selected conductor exponents and their certificates; lines 393–447 give
  `canonicalLocalQuasiCharData` and `canonicalLocalAddCharData`.
  File SHA-256:
  `2fb2122e528972c0d4fa834649e77c54cf94a6f446f44c8c1fe11e646a116ef7`.

These definitions adapt the role of those upstream canonical packages.
Deliberate modifications are the project namespace, explicit arbitrary
universe and supplied p-adic instances, direct reuse of the Library conductors
and agreement proofs, and the narrower Library additive input. Upstream takes
an arbitrary continuous complex-unit-valued additive character with a separate
nontriviality proof; here a nontrivial unitary Library character is transported
through `Circle.toUnits`. The multiplicative input retains every continuous
quasicharacter. This module does not port the upstream conductor existence
proofs or `Basic.StandardCharacterBridge`.

The retained license matches the original; the source has no `NOTICE`.
No applicable errata note was found in the current Library or project notes.
This module completes only the canonical-package portion of conductor reuse
unit 3 described in
[the public audit](../../../../notes/reuse/epsilon-fml-local-constant-audit.md).
It defines no finite local constant, `Delta`, epsilon factor, comparison
between such constants, First Main Lemma, or epsilon_SML content.
