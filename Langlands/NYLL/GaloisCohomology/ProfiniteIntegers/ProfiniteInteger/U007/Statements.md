# NYLL M009.007 target: reduction of an integer in `ℤ̂` modulo `n`

This module covers one theorem of Naganori Yamaguchi's ClassFieldTheory
(NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`. It discharges the
unit by reusing a published Library target, as the task's existing-declaration
route allows, and keeps the required name only as an alias of that target. It
contains no proof of the target.

## Source

The original is `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`
(271 lines, SHA-256
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory row is in `notes/reuse/nyll-public-port/m001-m024.md`, section M009
(patch status "none in patch10").

| Unit | Original name; docstring / attribute / asserted type / proof lines | Replacement | Required-name alias (paired Lean line) |
| --- | --- | --- | --- |
| M009.007 | `ClassFormation.zHatReduction_int`; 110 / `@[simp]` 111 / 112–115 / 116 (`rfl`) | published M008.019 target `Langlands.NYLL.ClassFormation.zHatReduction_intCastStatement` | `Langlands.NYLL.ClassFormation.zHatReduction_intStatement` (line 33) |

The source theorem is

```lean
@[simp]
theorem zHatReduction_int (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction n hn
        ((Int.castRingHom ZHat) a) =
      (a : ZMod n) :=
  rfl
```

in the context of source lines 22–26 (`namespace ClassFormation` and
`noncomputable section`). The file has no `variable`, `universe`, `open`,
`omit` or `include` command before line 116.

## Replacement and exact correspondence

The published M008.019 target, in
`Langlands/NYLL/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore/Statements.lean`,
is

```lean
def Langlands.NYLL.ClassFormation.zHatReduction_intCastStatement
    (n : ℕ) (hn : 0 < n) (a : ℤ) : Prop :=
  zHatReduction n hn (a : ZHat) = (a : ZMod n)
```

It has the source theorem's complete telescope: the explicit binders `n : ℕ`,
`hn : 0 < n` and `a : ℤ`, in the same order, with the same names, and no
universe parameters. Its body differs from the source assertion only in how
`a` enters `ZHat`. The source writes Mathlib's ring homomorphism
`(Int.castRingHom ZHat) a` and the published target writes the cast
`(a : ZHat)`. These are definitionally equal, since `Int.castRingHom` applies
`Int.cast`. The two propositions are therefore definitionally equal for every
`n`, `hn`, `a`, and so are the two complete target families. The difference
in notation is not a different statement. In the same way, the source's own
proof `rfl` and the published theorem's proof `rfl` prove the same
computation.

The published theorem
`Langlands.NYLL.ClassFormation.zHatReduction_intCast (n : ℕ) (hn : 0 < n) (a : ℤ) : zHatReduction_intCastStatement n hn a`
(`ProfiniteIntegerCore/U019/Proofs.lean`) therefore already proves M009.007.

## The alias

The task requires the name `Langlands.NYLL.ClassFormation.zHatReduction_intStatement`.
It is kept as a reducible alias of the replacement and is not an independent
target:

```lean
abbrev Langlands.NYLL.ClassFormation.zHatReduction_intStatement
    (n : ℕ) (hn : 0 < n) (a : ℤ) : Prop :=
  zHatReduction_intCastStatement n hn a
```

Its parameters are the source theorem's `n`, `hn`, `a`, in source order and
with the source binder kinds. Its value is the published target applied to
them, so `zHatReduction_intStatement = zHatReduction_intCastStatement` holds by
`rfl`. A term of `zHatReduction_intCastStatement n hn a`, in particular
`zHatReduction_intCast n hn a`, is a term of `zHatReduction_intStatement n hn a`.
No proof task for the alias is needed beyond the published theorem.

Here `ZHat` is the published M008 closure model
`Langlands.NYLL.ClassFormation.ZHat : Type 0`, the closure of the diagonal
image of `ℤ` in `∏_{n > 0} ZMod n`, with its published ring structure.
`zHatReduction n hn : ZHat →+ ZMod n` is the published M008 reduction modulo
`n`, the `n`-th coordinate, and it is continuous. The proposition says that
reducing the image of an integer `a` modulo a positive `n` gives the residue
of `a` in `ZMod n`.

## Modifications (Worker 5454)

- **Reuse**: the source assertion is not restated. The required name is a
  reducible alias (`abbrev`) of the published target
  `zHatReduction_intCastStatement`, applied to the source parameters.
- **Extraction**: the proof (`rfl`, line 116) and the `@[simp]` attribute
  (line 111) are omitted.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
  The source's `noncomputable section` is not reproduced, because the alias is
  a proposition and needs no noncomputable marking.
- **Imports**: the source imports four Mathlib modules and
  `Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore` (lines 7–11).
  The port imports only the published module
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements`,
  which supplies `zHatReduction_intCastStatement` and, through its import of
  the M008 Definitions module, `ZHat`, its ring structure and `zHatReduction`.
- **Docstring**: the source docstring "Establishes the identity …" is
  replaced by a target description with the same displayed formula, which
  states the reuse. The module docstring is a modification notice.

## Focused check

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection reports that
  `zHatReduction_intStatement` returns `Prop`.
- A private audit module copies the source theorem verbatim, with its source
  proof `rfl`, after `noncomputable section` as in the source. The copy sits
  in an auxiliary namespace nested in `Langlands.NYLL.ClassFormation`, so that
  `ZHat` and `zHatReduction` resolve to the published constants. A `MetaM`
  command checks the copy against a Prop-valued target: identical
  universe-parameter lists, identical binder names and binder kinds, and the
  theorem's type definitionally equal to `∀ n hn a, target n hn a`. It passed
  for the published replacement `zHatReduction_intCastStatement` and for the
  alias `zHatReduction_intStatement`. As a control, the same command rejected
  a variant of the M115.001 target with its parameters `K` and `L` swapped.
- In the same module, these checks compiled:
  `@zHatReduction_intStatement = @zHatReduction_intCastStatement := rfl`;
  the published `zHatReduction_intCast n hn a` as a proof of
  `zHatReduction_intStatement n hn a`; and the same term as a proof of the
  literal source assertion
  `zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`. A
  reducibility query confirmed that the alias is `reducible`.

The audit module is private and is not part of this contribution.

## Scope

This target asserts one computation in the published closure model of `ℤ̂`.
It does not assert a class-formation, cup-product, Tate, transfer or
reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"). The replacement target and the published
proof are Library modules by Workers 120 and 124. No other draft was reused.
The retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
