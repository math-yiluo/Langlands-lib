# Valuation-ring preservation from unique extension

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.MemValuationSubringAlgEquivIffOfHasUniqueValuationExtensionStatement`.
It adapts the signature of M304.003,
`RamificationTheory.DiscreteValuationField.DVF.mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension`,
from Naganori Yamaguchi's
[`RealLowerGroups.lean`, lines 70–86](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L70-L86),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete source file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
The original signature occupies lines 70–77; lines 78–86 supply its proof.
This module publishes the proposition for a separate proof unit.

## Complete quantified telescope

The existing `DVF` bundle is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`.
The imported
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.UniqueExtension`
provides the general uniqueness predicate in the statement's namespace.
With the bundle namespace opened, the complete definition is:

```lean
universe u v w x

def MemValuationSubringAlgEquivIffOfHasUniqueValuationExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (σ : L ≃ₐ[K] L) (z : L),
    z ∈ target.valuation.valuationSubring ↔
      σ z ∈ target.valuation.valuationSubring
```

The declaration has type `Prop` and no mathematical declaration parameters.
All mathematical binders occur inside its body, in the original order:
implicit field carriers, supplied field and algebra instances, implicit chosen
base and target bundles, the target-extension instance, explicit uniqueness
hypothesis, explicit algebra automorphism, and explicit element.

The four universe parameters are independent:

| Level | Role |
| --- | --- |
| `u` | Base field carrier `K`. |
| `v` | Chosen base value group `base.ValueGroup`. |
| `w` | Target field carrier `L`. |
| `x` | Chosen target value group `target.ValueGroup`. |

The published predicate has five universe parameters. Here it is used exactly
as `HasUniqueValuationExtension.{u, v, w, x, x}`: its comparison value group
also lives in `Type x`. Thus `huniq` quantifies over each implicit
`Gamma' : Type x`, its supplied `LinearOrderedCommGroupWithZero Gamma'`
instance, an explicit valuation `v' : Valuation L Gamma'`, and then an
instance `[base.valuation.HasExtension v']`, with conclusion
`target.valuation.IsEquiv v'`. There is no fifth independent universe in this
closed statement. Neither field nor value-group universe is fixed to `0`.

## Hypotheses and exact conclusion

Each DVF stores a chosen valuation and its rank-one discreteness proof.
The separate instance premise
`base.valuation.HasExtension target.valuation` is Mathlib's extension
relation along the actual `algebraMap K L` from the supplied algebra. Its
field asserts

```lean
base.valuation.IsEquiv (target.valuation.comap (algebraMap K L))
```

Here `Valuation.IsEquiv` compares the two valuations' order relations:
`∀ a b, v₁ a ≤ v₁ b ↔ v₂ a ≤ v₂ b`. The chosen value groups may differ.
The uniqueness predicate alone neither assumes nor asserts that the chosen
target extends the base, so the explicit extension instance remains essential
in this statement.

The conclusion refers to Mathlib's actual
`target.valuation.valuationSubring : ValuationSubring L`, the subring with
underlying set `{z : L | target.valuation z ≤ 1}`. It asserts, in this order,
that membership of `z` is equivalent to membership of `σ z`. The supplied
`σ : L ≃ₐ[K] L` uses the same algebra structure and fixes its scalar image.
No abstract action or separate preservation certificate replaces these data.
Preservation is the conclusion to be derived from extension and uniqueness.

No finite-dimensionality, separability, completeness, Henselianity, local-field
or Galois hypothesis is added. The proposition concerns arbitrary supplied
base and target DVFs and arbitrary algebra automorphisms and elements.

## Source correspondence and proof boundary

| Original at the pinned commit | Adaptation |
| --- | --- |
| Namespace `RamificationTheory.DiscreteValuationField.DVF`, lines 35–39 | Add the `Langlands.NYLL` prefix; retain the namespace structure and open the published bundle namespace. |
| Universe and field/instance context, lines 33 and 41 | Retain the four universes used by M304.003 and move the implicit fields and supplied instances inside the closed Prop. |
| M304.003 bundle, extension and uniqueness binders, lines 71–74 | Preserve implicit bundles, the actual extension instance and explicit `huniq`, including comparison universe `x`. |
| M304.003 automorphism, element and conclusion, lines 75–77 | Preserve explicit `σ` and `z`, the chosen target subring, and the iff direction. |
| M304.003 proof, lines 78–86 | Omitted from this statement unit; reserved for the separate exact-target proof. |

The original proof pulls the target valuation back along `σ`, uses extension
compatibility and `huniq`, and obtains equality of valuation subrings using
Mathlib's `Valuation.isEquiv_iff_valuationSubring`. The comparison valuation
has the same value-group universe `x`, explaining the exact uniqueness
specialization.

The already published generic theorem
`Langlands.NYLL.LocalFieldTheory.hasExtension_comap_ringEquivs` covers the
transport needed for M304.002. A future proof can specialize it to the
identity base equivalence and `σ.toRingEquiv`, using `σ.commutes`, and then
apply uniqueness and equality of valuation subrings. This module imports only
the published uniqueness predicate and `Mathlib.Algebra.Algebra.Equiv`.
It adds one Prop definition. It adds no transport target, proof theorem,
instance, induced ring automorphism or ramification-group construction.

## Provenance, attribution and modifications

Worker 1199 extracted the signature and wrote this explanation on
1 November 2026. Worker 106 supplied the exact closed target formulation and
the generic transport reuse route. The adaptation replaces the upstream
imports with the published predicate and focused Mathlib support, prefixes
the namespace, moves all mathematical parameters into the proposition,
changes the declaration name to the requested statement name, and omits the
proof, unused fifth universe, noncomputable section and pointwise scope.
The unused-variable linter is disabled locally for this definition to retain
the source's explicit hypothesis name `huniq` in the proposition's telescope.
The source hypotheses and conclusion have no mathematical change. The source
partition records no patch10 change for M304.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by OpenAI
Codex). The source is Apache-2.0. Verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) copies remain in the Library.
The original NOTICE has no source-specific entry for `RealLowerGroups.lean`.
No applicable errata were found in the project or published errata locations.
