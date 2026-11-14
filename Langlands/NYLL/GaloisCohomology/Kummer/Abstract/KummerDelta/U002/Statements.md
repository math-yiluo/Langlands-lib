# NYLL M023.002 target: membership in the ambient fixed additive subgroup

This module extracts one theorem type from Naganori Yamaguchi's
ClassFieldTheory (NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`, as
a Prop-valued definition. It supplies the target only and contains no proof
of it. The proof is separate `lean.proof@1` work.

## Source

The original is `Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean`
(178 lines, SHA-256
`6778a3be3b28518c10a0288dd21befed505cf6bed556590eab1f4dba82f166b8`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory row is in `notes/reuse/nyll-public-port/m001-m024.md`, section M023.

The inventory gives this module patch status `P1`. According to
`notes/reuse/nyll-public-port-plan.md` (patch table, row P1), P1 replaces the
missing `AddMonoidHom.ofClass` by `AddMonoidHomClass.toAddMonoidHom wp.hom`.
`AddMonoidHom.ofClass` occurs only at source lines 61, 69, 87, 95, 100 and
135, in the later declarations M023.003–M023.007. It does not occur in the
statement or proof of M023.002 (lines 46–53), so P1 does not apply to this
unit.

| Unit | Original name; docstring / attribute / asserted type / proof lines | Target (paired Lean line) |
| --- | --- | --- |
| M023.002 | `KummerTheory.mem_ambientFixedAddSubgroup_iff`; 46–47 / `@[simp]` 48 / 49–52 / 53 (`Iff.rfl`) | `Langlands.NYLL.KummerTheory.mem_ambientFixedAddSubgroup_iffStatement` (line 33) |

The section context is source lines 22–30: `namespace KummerTheory`,
`open CyclicCohomology`, `noncomputable section` and the only `variable`
command of the file,
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 30). There is no `omit`, `include` or `universe` command.

## Exact statement

```lean
def Langlands.NYLL.KummerTheory.mem_ambientFixedAddSubgroup_iffStatement
    {G : Langlands.NYLL.IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (H : ClosedSubgroup G) (a : A.V) : Prop :=
  a ∈ ambientFixedAddSubgroup A H ↔ ∀ h : H.toSubgroup, A.ρ h.1 a = a
```

The paired Lean file keeps the source's `variable` command of line 30
verbatim (paired line 29). The theorem mentions `G`, so Lean includes the
three section variables, as in the source, and the full telescope is the one
displayed: the three section variables in the source order and binder kinds,
then the theorem's own `A`, `H` and `a`. `IntegralRepGroupType` is the
published alias `Langlands.NYLL.IntegralRepGroupType := Type 0`, and
`ambientFixedAddSubgroup A H` is the published M023.001 definition: the
additive subgroup of `A.V` of elements fixed by every element of the closed
subgroup `H`. The proposition says that `a` lies in this subgroup if and only
if `A.ρ h a = a` for every `h ∈ H`.

The target has one universe parameter, `u_1`: `Rep ℤ G` is Mathlib's
`Rep.{u} ℤ G`, and Lean generalizes the universe `u` of the representation
space `A.V` automatically, exactly as in the source theorem (and in the
published M023.001 definition). Inspection reports the level parameter list
`[u_1]`.

## Modifications (Worker 5454)

- **Extraction**: only the asserted type is taken. The proof (`Iff.rfl`, line
  53) and the `@[simp]` attribute (line 48), which has no meaning on a
  Prop-valued definition, are omitted.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
  `noncomputable section` and the `variable` command are kept.
  `open CyclicCohomology` (line 24) is omitted because the statement uses
  nothing from that namespace; the published M023.001 module omits it for the
  same reason.
- **Imports**: the source imports three NYLL modules (lines 7–9). The port
  imports only the published M023.001 module
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`,
  which supplies `ambientFixedAddSubgroup` and, through its imports,
  `IntegralRepGroupType`, `Rep` and `ClosedSubgroup`.
- **Docstrings**: the declaration docstring is the source theorem docstring.
  The module docstring is a modification notice.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection reports that
  the target returns `Prop`.
- A private audit module copies the source theorem with its source proof
  `Iff.rfl`, after `open CyclicCohomology`, `noncomputable section` and the
  `variable` command of line 30, as in the source, into an auxiliary
  namespace nested in `Langlands.NYLL.KummerTheory`, so that
  `ambientFixedAddSubgroup` resolves to the published constant. A `MetaM`
  command then checks that the theorem and the target have identical
  universe-parameter lists, identical binder names (after erasing hygienic
  macro scopes) and binder kinds along the whole telescope, and that the
  theorem's type is definitionally equal to `∀ xs, target xs`. It passed. As
  a control, a variant of the M115.001 target with its parameters `K` and `L`
  swapped was rejected by the same command.
- A second private module proves the target, applied to its parameters, by
  the source proof `Iff.rfl`. That proof is not part of this contribution.

## Scope

This target is the membership characterization of one additive subgroup. It
does not assert a Kummer-theory, class-formation, cup-product, Tate, transfer
or reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. Patch P1 does not affect
this unit (see above), and no other draft was reused. The retained license
and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
