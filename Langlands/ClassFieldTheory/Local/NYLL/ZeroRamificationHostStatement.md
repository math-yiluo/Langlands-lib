# Zero-depth ramification in terms of supplied local-field data

This module defines one closed proposition,
`Langlands.LocalClassField.NYLL.ZeroUpperRamificationHostStatement : Prop`.
It says that the zeroth upper ramification group of a finite Galois extension of
universe-zero p-adic fields consists exactly of the automorphisms that act
trivially modulo the maximal ideal on every integral element. The group is the
published NYLL one, built from the supplied base data `TF`. The integrality
and congruence conditions are measured by an arbitrary, separately supplied
extension datum `TE`. The file contains no proof.

## Complete proposition

Inside `Langlands.LocalClassField.NYLL` the complete definition is:

```lean
def ZeroUpperRamificationHostStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F E : PadicField.{0} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsGalois F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData) (σ : Gal(E.Carrier/F.Carrier)),
    letI := TF.topology
    letI := TF.valuativeRel
    letI := TF.localField
    σ ∈ Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup
        F.Carrier E.Carrier 0 ↔
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation (σ x - x) < 1
```

All binders are quantified inside the proposition; the definition has no
parameters and no universe parameters.

| Binder | Meaning |
| --- | --- |
| `p`, `[Fact p.Prime]` | Every prime |
| `F E : PadicField.{0} p` | Finite extensions of `Padic p` whose carriers lie in `Type` |
| `[Algebra F.Carrier E.Carrier]` | The given field embedding |
| `[IsScalarTower (Padic p) F.Carrier E.Carrier]` | Compatibility of that embedding with the `Padic p` structures |
| `[FiniteDimensional F.Carrier E.Carrier]`, `[IsGalois F.Carrier E.Carrier]` | `E/F` is finite Galois |
| `TF : F.TopologicalData` | Arbitrary supplied local-field realization of the base |
| `TE : E.TopologicalData` | Arbitrary supplied local-field realization of the extension |
| `σ : Gal(E.Carrier/F.Carrier)` | An actual `F`-algebra automorphism of `E` |

The three `letI` lines install the topology, valuative relation and
nonarchimedean local-field structure carried by `TF` on `F.Carrier`. These are
exactly the base structures that the NYLL group needs. The fields lie in `Type`
because `localUpperRamificationGroup` is defined only for `K L : Type`. The
statement needs only a Galois extension, not an abelian one, so it applies in
particular under the `IsAbelianGalois` hypotheses of the host reciprocity Props.

## The two sides

**Left side.** `localUpperRamificationGroup K L t` is the published adaptation
of NYLL M327.005, in
`Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions`.
Its base is the canonical complete discretely valued field
`localCompleteDVF K`, whose valuation is `ValuativeRel.valuation K`. Here that
valuation comes from `TF.valuativeRel`. Its target is the named chosen extension
`chosenLocalExtensionCompleteDVF K L` with its chosen valuation. The group is
taken at real index `0`. No structure on `E.Carrier` other than the field
embedding enters the left side. In particular, it does not depend on `TE`.

**Right side.** This is word for word the right side of the inertia clause of
`Langlands.LocalClassField.FiniteAbelianReciprocity` in
`Langlands/ClassFieldTheory/Local/FiniteReciprocityStatement.lean`, lines 36–37.
`TE.discreteValuation` is the multiplicative `ℤᵐ⁰`-valued discrete valuation of
the supplied extension datum. Its closed unit ball is the supplied integer ring
`TE.Integers`, and its open unit ball is the maximal ideal of that ring. The
condition therefore says that `σ x ≡ x` modulo the maximal ideal for every
integral `x`, that is, that `σ` acts trivially on the supplied residue field.
The value `x = 0` is allowed and satisfies the condition trivially.

The left side uses NYLL's chosen extension valuation and the right side an
arbitrary supplied one. So the proposition also contains the comparison of the
two valuations of `E`. This comparison is to be proved, not assumed: no
valuation-extension, integral-closure, finite integer-module or residue
comparison appears as a premise.

## Role in the finite reciprocity programme and intended proof route

This target is a derived host-facing formulation used for the zero-depth
inertia clause of `FiniteAbelianReciprocityTypeZeroStatement`. The source
filtered reciprocity theorem `finiteAbelian_filteredLocalReciprocity`
(`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean`)
at `t = 0` identifies `localUpperRamificationGroup K L 0` with the image under
the NYLL Artin map of the valuation units. Together with that theorem and the
named quotient evaluation, this proposition will turn that group identity into
the right side of the host inertia clause. The Artin map, the filtered theorem
and the quotient equivalence are not yet published. They are neither used nor
assumed here.

The intended proof, which is a separate later task and is not claimed here,
proceeds as follows. Install `TE.topology`, `TE.valuativeRel` and
`TE.localField` on `E.Carrier`. Take the valuation extension from the published
`suppliedRelativeValuationExtension`, and the integral-closure and
module-finiteness instances from the published `relativeIntegerStructure`,
after identifying its explicit relative integer algebras with Mathlib's
valuation-integer algebra structures. Then rewrite with the published
`localUpperRamificationGroup_zero_eq_residue_ker` (M328.002) and the residue
kernel characterization
`galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal`
(M160.018). Finally, translate integral elements and maximal-ideal membership
into the two `TE.discreteValuation` inequalities through the order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` used to define
`discreteValuation`.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions`
  supplies `localUpperRamificationGroup` and its published dependencies.
- `Langlands.LocalField.Normalization.Definitions` supplies `PadicField`,
  `TopologicalData` and `TopologicalData.discreteValuation`.

Both modules are used unchanged. No instance, alias or definition is added.

## Provenance and source correspondence

The proposition is derived. No NYLL source declaration has this form. The
closest is M328.002, `RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker`,
at lines 96–111 of
`Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean` in Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. It is retained in registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`). Its
conclusion identifies the same upper group at `0` with the kernel of the residue
action of a valuation `L` carries as instance data. The present statement makes
three changes, all derived. It replaces that instance valuation by an arbitrary
host `TE`. It removes the valuation-extension, integral-closure and
module-finiteness hypotheses, which hold for supplied data. And it writes the
residue kernel as the host congruence. The upper-group definition is M327.005,
lines 102–113 of
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean` in the same commit.
Worker 10 read both passages in the pinned copy. No NYLL source code is copied
into this file. No errata file exists for this source in the Library's
`notes/errata`.

The mathematical content is classical: the zeroth ramification group of a
finite Galois extension of local fields is its inertia group, the kernel of
the action on the residue field, and upper and lower numbering agree at `0`.
The host Markdown `FiniteReciprocityStatement.md` records the original-source
locations in Serre's *Local Fields* for the host inertia clause. This pair
claims no further reading of Serre.

## Author verification and status

`lean_check` in the approved environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the
module with no errors and no diagnostics in this file. The only warning in the
build is an unused-variable lint in the already published dependency
`Langlands/NYLL/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure/MaximalIdealCompletenessStatements.lean`.
Inspection of the unapplied declaration
reported kind `definition`, no level parameters, `statement_returns_prop: true`,
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. A private
draft proof following the route above also compiled with the same three
axioms. That draft is not part of this submission, and it is no evidence of
acceptance. Independent semantic review, publication and a separate exact-target
proof remain required. This pair proves no reciprocity, inertia-image,
universe-transport or Weil result.

Worker 10 designed and wrote this pair for task
`34dfcbc7-f6ed-46fd-84e3-4d89df60fe8e` (NYLL finite reciprocity 4f).
