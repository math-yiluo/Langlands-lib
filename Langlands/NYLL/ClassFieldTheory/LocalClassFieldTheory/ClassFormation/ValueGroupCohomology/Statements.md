# NYLL M141: value-group norm and surjectivity targets

The first proposition says that the additive value of the finite-group norm
on the trivially acted-on multiplicative integer value group is the order
of `Gal(L / K)` times the additive input. The second says that the reduction
homomorphism on the fixed subgroup is surjective. Both are targets for later
proofs, with the source propositions as their bodies, including the source
`letI` action bindings.

The fields share the arbitrary universe `u`. The complete source telescope
is explicit `K L : Type u`, then `[Field K] [Field L] [Algebra K L]` and
`[FiniteDimensional K L]`, in that order. The norm target also has explicit
`a : Multiplicative Int` after these instances. No Galois-extension,
valuation, topology or local-field hypothesis is added. Finite-dimensionality
supplies the source's canonical finite automorphism-group instance; no
separate `Fintype` argument is added.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean`.
Original file SHA-256:
`6ee54afe1a8a664d94bff689a3725f8fa4a92aa4054f0f371c7d199074ec59e9`.
The original is retained under registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` and the path above.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The full shared source context is lines 16–31.

| Unit | Original name | Source statement lines | Adapted name |
| --- | --- | --- | --- |
| M141.001 | `LocalClassFieldTheory.galoisGroupValueGroup_tateNorm_toAdd` | 35–39 | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroup_tateNorm_toAddStatement` |
| M141.003 | `LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom_surjective` | 60–62 | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom_surjectiveStatement` |

## Complete Lean context and declarations

```lean
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

universe u

open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

def galoisGroupValueGroup_tateNorm_toAddStatement (a : Multiplicative Int) : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Multiplicative.toAdd
        (tateNorm (Gal(L / K)) (Multiplicative Int) a) =
      (Fintype.card (Gal(L / K)) : Int) * Multiplicative.toAdd a

def galoisGroupValueGroupFixedToZModHom_surjectiveStatement : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Function.Surjective (galoisGroupValueGroupFixedToZModHom K L)
```

## Modification record and reuse

Worker 230 extracted only the listed units and prefixed the namespace and
opens with `Langlands.NYLL`. The source section context and variable telescope
are retained. Each source `theorem name : P := by ...` becomes
`def nameStatement : Prop := P`; the proofs are omitted.

The reduced imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Definitions`

The actual action is
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction`
from `Valuation.Definitions` under the same ClassFormation module path.
The actual finite-product norm `tateNorm` and actual fixed-point subgroup
`fixedSubgroup` are reused from
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` in the
M113 `HerbrandLowDegree.Basic.Definitions` module. The reduction homomorphism
uses Mathlib's `Int.castAddHom`, `AddMonoidHom.toMultiplicative` and the actual
subgroup inclusion. No substitute for an unpublished theorem proof or any
global instance is introduced. The source module docstring is replaced by
the explicit extraction record.

## Attribution and scope

The original copyright and author header is retained verbatim, with a
modification header. The published `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained. This unit discharges no host
class-formation, reciprocity, Tate, transfer or cup-product target.
