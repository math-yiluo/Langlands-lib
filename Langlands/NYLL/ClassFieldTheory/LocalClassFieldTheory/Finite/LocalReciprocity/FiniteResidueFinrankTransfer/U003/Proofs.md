# Naturality of the literal-to-intrinsic residue equivalence: proof of M252.003

The theorem
`Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMap`
proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U003.Statements`).
It has the universe parameters `u v` and the binders of the target, in the
same order and with the same binder kinds:

```lean
theorem residueFieldEquivDecompositionResidueOfEqTop_algebraMap
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) (x : C) :
    residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement
      A C hC hA x
```

Let `Ω / F` be a Galois extension, `A` a valuation subring of `Ω` and `C` a
valuation subring of `F` with `A ∩ F = C` (`hC`), and suppose the
decomposition group of `A` over `F` is the whole Galois group (`hA`). For
`x ∈ C`, the theorem states: reducing `x` in the residue field of `C`,
applying the published equivalence
`residueFieldEquivDecompositionResidueOfEqTop A C hC hA` (M252.002) into the
intrinsic residue field `κ_F = decompositionResidueField F A`, and then the
structure map `κ_F → λ` into `λ = selectedResidueField A`, gives the residue
class in `λ` of `x` viewed as an element of `A`. The statement and every
module it imports are unchanged.

## The implemented proof

The proof is `rfl`, as in the source. The two sides are definitionally equal
because every map involved is defined on representatives:

- M252.002 is `IsLocalRing.ResidueField.mapEquiv` of the M252.001 equivalence
  `C ≃+* decompositionFieldValuationSubring F A` (which sends `x` to the image
  of `x` in the decomposition field), followed by the published
  `decompositionFieldResidueEquiv (K := F) A` (M243.018), itself a
  `mapEquiv` of the comparison with the decomposition-fixed subring of `A`
  followed by Mathlib's `Ideal.quotientEquivAlgOfEq`. Applied to the residue
  class of `x`, this is the class of `algebraMap F Ω x` in the quotient
  `κ_F` of the decomposition-fixed subring.
- The structure map is the published instance
  `selectedResidueField.instAlgebra F A` (M243.021), Mathlib's
  `Ideal.Quotient.algebraQuotientOfLEComap`, which sends the class of `a` to
  the residue class of `a` in `λ = IsLocalRing.ResidueField A`.

So the left side reduces to the residue class of the element of `A` with
underlying value `algebraMap F Ω x`, which is the right side; the membership
proofs agree by proof irrelevance. The kernel checks the definitional
unfolding.

The development check in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(diagnostic `4a3fac17-a92a-458b-9155-ee7369ba152c`) reports 0 errors and
0 warnings. The theorem uses only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Dependencies

| Role | Declaration | Module |
| --- | --- | --- |
| target | `Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U003.Statements` |
| M252.002 (unfolded) | `Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop` | `...LocalReciprocity.FiniteResidueFinrankTransfer.U002.Definitions` |
| M252.001 (unfolded) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop` | `...LocalReciprocity.FiniteResidueFinrankTransfer.U001.Definitions` |
| M243.018 (unfolded) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFieldResidueEquiv` | `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison` |
| M243.003/.004, M243.020/.021 | `decompositionResidueField`, `selectedResidueField` and their `instField`/`instAlgebra` instances, under `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring` | `...ResidueExactSequence.Definitions` and `...ResidueExactSequence.ResidueFields` |

The only direct import is the statement module; every other module above is
reached through it. This module declares only the theorem above; it adds no
instance and no other declaration.

## Source correspondence and adaptation

The source is the theorem
`LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMap`
(inventory M252.003), lines 103–120 of the pinned source file: docstring
lines 103–104, signature lines 105–119, proof `rfl` at line 120. The binders,
universes `u v`, docstring and proof are the source ones. The adaptations
are:

- the type is written as the published target applied to the binders,
  `residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement A C hC hA x`,
  whose body is the source type unchanged; `rfl` unfolds the target as well;
- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- of the source opens (lines 23–32) only `open RamificationTheory` and
  `open HilbertRamification.ValuationSubring` are kept, as in the target
  module; `CyclicCohomology`, `ClassFormation`, `LocalFieldTheory`,
  `ValuationTheory` and the scoped `ValuativeRel` notation are not needed;
- the source imports are replaced by the published target module.

The adapted name is the one reserved in row M252.003 of
`notes/reuse/nyll-public-port/m241-m258.md`. Worker 85 checked this proof
against the exact target (diagnostic `758d36bf`) and described it in the task
context. Worker 122 wrote and checked this implementation.

## Use downstream

In the source, the proof of `localResidueDatum_residueDegree_eq_residueFinrank`
(M252.004) rewrites with this naturality square, as do proofs in
`FixedFieldLocalData.lean`.

## Original source and license

Naganori Yamaguchi (assisted by OpenAI Codex), *ClassFieldTheory (NYLL)*,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`, lines 103–120](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean#L103-L120).
The retained copy has SHA-256
`2a282f270893fba7c9c47573e1f5dad6ac27f8310981b0bb61f251fbe38b46ed`. Its
lines 1–40 (header, imports, namespace, opens, universes) and 95–125 were
read. The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records the modifications by Worker 122 on 15 November 2026. The
existing [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This is a residue-field support result. It asserts nothing about host
reciprocity or class formations.
