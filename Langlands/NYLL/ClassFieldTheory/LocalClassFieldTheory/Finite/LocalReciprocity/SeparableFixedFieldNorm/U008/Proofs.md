# NYLL M165.008: the coset action on units is evaluation under the embedding (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement`
([target](../U006/Statements.md), NYLL source unit M165.008) by the theorem

```lean
theorem relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω)
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) :
    relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement
      K Ω E x q
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
Its binders are those of the target, in the same order and with the same
binder kinds, and its type is the target applied to them. Neither has a
level parameter.

The theorem says the following. Let `Ω / K` be a Galois extension and `E` an
intermediate field. Write `G = Gal(Ω / K)`, presented as the subgroup
`(closedFixingSubgroup K Ω ⊥).toSubgroup`, and `H = Gal(Ω / E)`. Let
`x ∈ Eˣ` and let `q = σH` be a left coset. Then the published abstract coset
action `relativeCosetAction` of `q` on `x`, with `x` viewed as an
`H`-fixed unit of `Ω` and the result viewed as an element of `Ω`, equals
`σ|_E (x)`. Here `σ|_E = baseFixingCosetToAlgHom K Ω E q` is the
`K`-embedding of `E` into `Ω` attached to `q`. No separable-closedness,
finiteness or separability hypothesis is used, despite the source name.

## Proof

The proof is the source tactic proof, unchanged:

```lean
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl
```

1. The coset type `G ⧸ H` is a quotient type. Mathlib's
   `Quotient.inductionOn'` reduces the claim for an arbitrary coset `q` to
   the claim for the coset of a representative `σ : G`.
2. For that coset, both sides reduce to the same element of `Ω` by unfolding
   definitions, so `rfl` closes the goal; Lean unfolds the target `def`
   itself during this definitional check. On the left, the published
   `relativeCosetAction` (M024.001) is defined by `Quotient.liftOn'`, so on
   the coset of `σ` it computes to `A.ρ σ.1 a.1`. Here `A` is
   `galoisAmbientUnitsRep K Ω`, the abbreviation for Mathlib's
   `Rep.ofAlgebraAutOnUnits K Ω`, in which `σ` acts on `Ωˣ` by applying `σ`.
   The element `a` is `intermediateFieldUnitsEquivGaloisFixed K Ω E
   (Additive.ofMul x)`, whose underlying unit of `Ω` is the image of `x`
   under the inclusion `E → Ω`. On the right, the published
   `baseFixingCosetToAlgHom` (M165.001) is also defined by
   `Quotient.liftOn'`, and on the coset of `σ` it is
   `σ.1.toAlgHom.comp E.val`. Evaluated at `(x : E)`, this is `σ` applied to
   `x` viewed in `Ω`.

## Dependencies

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U006.Statements`
  is the published target, and the only import. Through it come the
  published definitions that occur in the target and that `rfl` unfolds:
  `relativeCosetAction`, `galoisAmbientUnitsRep`,
  `intermediateFieldUnitsEquivGaloisFixed`, `baseFixingCosetToAlgHom`,
  `closedFixingSubgroup`, `extensionSubgroup` and `fixingSubgroupLeBase`.
- From Mathlib: `Quotient.inductionOn'`.

No other Library result and no helper declaration is used. The published
target and definitions are used by name and none of them is modified. In
particular the proof does not use the M165.006 instance or
`baseFixingCosetEquivAlgHom`. The module opens `RamificationTheory`,
`CyclicCohomology` and `ClassFormation`, as the target module does. The
first two make `closedFixingSubgroup` and `extensionSubgroup` in the binder
`q` resolve to the published names; the theorem itself mentions nothing from
`ClassFormation`.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with zero errors and zero warnings. Inspection of the theorem reported kind
`theorem`, no level parameters, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not
acceptance.

## Source correspondence and modification record

The original declaration is the theorem
`LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable`
in Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean#L178-L197)
(SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`).
It sits in `section NormAsProduct` (line 166). The line
`omit [IsSepClosed Ω] [FiniteDimensional K E] [Algebra.IsSeparable K E] in`
is line 178, the docstring lines 179–180, the statement lines 181–194 and the
proof lines 195–197. It uses the file-level section variables at lines 36–37
and the section variables at lines 175–176, minus the three omitted ones.

| Original declaration | Adapted declaration |
| --- | --- |
| `theorem LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable` (M165.008) | `theorem Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable` (this module) |
| `LocalClassFieldTheory.baseFixingCosetToAlgHom` (M165.001, in the statement) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom` (published) |
| `ClassFormation.relativeCosetAction` (M024.001, in the statement) | `Langlands.NYLL.ClassFormation.relativeCosetAction` (published) |
| `LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` (M088.006, in the statement) | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` (published) |
| `LocalClassFieldTheory.galoisAmbientUnitsRep` (M088.001, in the statement) | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep` (published) |

Worker 368 made these changes on 15 November 2026:

- the section variables that remain after the `omit ... in` line are written
  as explicit binders, in the source order, followed by the theorem's own
  binders `x` and `q`, as in the target. The conclusion is written as the
  target applied to these binders;
- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the source imports are replaced by the published target module. Of the
  source's opens, `RamificationTheory`, `CyclicCohomology` and
  `ClassFormation` are kept, as in the target module; the
  `noncomputable section`, the section structure, the `omit ... in` line
  (made unnecessary by the explicit binders) and the local instance
  `finiteSeparableAlgHomFintype` (M165.007, not used by this theorem) are
  omitted;
- the docstring and the tactic proof are the source's, unchanged.

The registered source is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
unchanged in the Library. This support proof discharges no host
class-formation, cohomology or reciprocity target.
