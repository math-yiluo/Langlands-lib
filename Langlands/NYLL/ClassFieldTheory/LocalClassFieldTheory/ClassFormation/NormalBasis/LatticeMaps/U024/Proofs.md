# The lattice Galois action agrees with the ambient action

This module proves
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe`,
the proof phase of M152.024 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m152).
Its type is exactly the target
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coeStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe
    (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coeStatement K L τ x
```

The section variables and the `omit` line are those of the target module, so
the parameters are the target's parameters in the target's order: a finite
Galois extension `L/K` of fields in one universe `u`, with a
`ValuativeRel K` instance, a Galois element `τ` and an element `x` of the
normal-basis lattice. The topology and local-field instances of the section
are omitted, as in the target. The target unfolds to

```lean
((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x :
  chosenNormalBasisIntegerLattice K L) : L) = τ (x : L)
```

that is, the restricted action of `τ` on the lattice, viewed in `L`, is the
action of `τ` on `L`. No hypothesis is added.

## Implemented proof

```lean
  rfl
```

The published definition `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ`
(M152.023, module `...NormalBasis.LatticeMaps.Definitions`) is the
`𝒪[K]`-linear equivalence whose forward function is
`fun x => ⟨τ (x : L), _⟩`. Applying it to `x` and coercing to `L` therefore
reduces definitionally to `τ (x : L)`, and `rfl` closes the goal. No
auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean#L430-L437):
the `omit` line at line 430, the docstring at line 431, the `@[simp]`
attribute at line 432 and the theorem at lines 433–437 (telescope and
conclusion at 433–436, proof term `rfl` at 437), under the section variables
at lines 28–29 and 62; the task's unit range 433–441 ends before the next
declaration at 442. The retained original file has SHA-256
`affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`. The
source proof is `rfl`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe` |
| Its statement | `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coeStatement K L τ x` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; keep the source section variables and `omit` line; give
the theorem the target applied to its parameters as its type; omit the
`@[simp]` attribute, because the theorem's type is a `Statement`
application; import only the target module; omit the source
`noncomputable section` and all other source declarations. The name,
docstring, telescope and the proof `rfl` are unchanged. The partition
records no patch10 change to this module.

## Imports

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Statements`
  supplies the target and, through `...NormalBasis.LatticeMaps.Definitions`,
  the equivalence `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv` and
  the lattice `chosenNormalBasisIntegerLattice`.

This module and everything it imports are left unchanged.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", released under Apache-2.0. The Lean file carries the dated
modification record. The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker
750 adapted this proof directly from the pinned original. The statement is
Worker 5264's, used unchanged.

This module proves only M152.024; M152.025, M152.026 and the coordinate rule
M152.027 are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
