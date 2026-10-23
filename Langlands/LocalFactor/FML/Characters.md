# FML character types and transport from Library characters

This module defines the character interface in namespace `Langlands.FML` and
imports the existing `Langlands.HarmonicAnalysis.Basic` interface. Its domain
types have arbitrary universe `u`.

## Character interface

`phase : ℂ → ℂ` is the total phase: it is `1` at zero and
`z / (‖z‖ : ℂ)` elsewhere. `phase_zero` and `phase_of_ne_zero` record those
branches. No norm or local-constant comparison theorem is asserted here.

For `[AddMonoid A] [TopologicalSpace A]`,
`ContinuousAddChar A` is the subtype
`{ψ : AddChar A ℂˣ // Continuous ψ}`. Its values are complex units.
The type includes the trivial character and does not itself impose
nontriviality or unit modulus.

The pointwise continuous-character submonoid gives a `CommMonoid` instance;
under `[AddCommGroup A]` the corresponding subgroup gives `CommGroup`.
The `FunLike` and `ContinuousMapClass` instances provide evaluation and
continuity. In namespace `ContinuousAddChar`, the retained interface is
`ext`, `toAddChar`, `toAddChar_apply`, `map_zero_eq_one`, `map_add_eq_mul`,
`continuous` and `one_apply`. The proofs use the subtype structure and
Mathlib's underlying additive-character laws.

For `[Monoid F] [TopologicalSpace F]`, `ContinuousQuasiChar F` abbreviates
`ContinuousMonoidHom Fˣ ℂˣ`. On a field, this is definitionally the existing
`Langlands.HarmonicAnalysis.Quasicharacter F`.
`quasicharacterIdentification F` is the identity function from that Library
type to this abbreviation; no new quasicharacter structure is introduced.

## Unitary additive-character transport

For `[AddGroup A] [TopologicalSpace A]` and
`ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter A`,
`ofUnitaryAdditiveCharacter ψ : ContinuousAddChar A` is constructed by
`Circle.toUnits.compAddChar ψ.toAddChar`. The Library input carries both
continuity and the nontriviality condition `ψ.toAddChar ≠ 1`.

The defining formulas are

```lean
ofUnitaryAdditiveCharacter ψ x = Circle.toUnits (ψ x)
(ofUnitaryAdditiveCharacter ψ x : ℂ) = (ψ x : ℂ)
```

They are proved by reflexivity in `ofUnitaryAdditiveCharacter_apply` and
`ofUnitaryAdditiveCharacter_coe_apply`. Continuity into the units topology is
proved with `Units.continuous_iff`: the complex-valued evaluation is continuous
by composition with subtype inclusion, and its inverse is continuous because
circle values are nonzero.

`circle_toUnits_injective` is Mathlib's actual
`unitSphereToUnits_injective` theorem specialized to `Circle.toUnits`.
`ofUnitaryAdditiveCharacter_ne_one` proves the transported character is
nontrivial. If it were `1`, evaluation and this injectivity would make every
value of the original additive character equal to `1`; `AddChar.ext` would
contradict the input's `nontrivial` field. This bridge retains the Library
character's hypotheses and uses no choice of conductor.

## Source and modifications

The phase and character constructors are adapted by Worker 20 from Fukuhiro
Ueda, *epsilon_FML*, commit
`0b4159be50e1bd45ddff1de4280399576a3e2024`, Apache-2.0.
The unchanged license is [LICENSE](LICENSE). The registered source
`external-lean-reuse-snapshots-2026-10-21` has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Locations relative to
`fukubillueda-web--epsilon_FML/source/LanglandsFirstMainLemma/` are:

- `Basic/Phase.lean`, lines 13–24: the definition and its two branch laws.
  File SHA-256:
  `80c59c74cc6aea826737bb4e7ce810ec08fbc3e5693927248949ab431de78fe1`.
- `Basic/CharacterTypes.lean`, lines 21–100 and 108–111: the two character
  types, instances and retained basic API. File SHA-256:
  `125166bc859fe247c7f006fb55a02e20d4a8da25e32002dcfa38b704abfe6c0d`.

Modifications are the project namespace, explicit universe, targeted Library
import and selection of the constructor API. The transparent quasicharacter
identification and unitary additive-character bridge are internal integration
definitions and proofs by Worker 20, derived from the existing Library
`UnitaryAdditiveCharacter` and `Quasicharacter` definitions and the cited
Mathlib operations. They are not attributed as upstream results. The module
does not import or reproduce `CharacterConductorExistence` or
`StandardCharacterBridge`.
