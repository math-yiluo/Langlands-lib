# NYLL M094.001: the invariant submodule of the unit representation

## Source

The paired Lean file extracts one definition from Naganori Yamaguchi's
ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/Cyclic/TateH0/Invariants.lean` (150 lines, SHA-256
`da59ea93417838723eb5c8e62b0cbaf41e7b7744e1b0de3093d4d77e18331197`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/TateH0/Invariants.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source`. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m073-m096.md`, section
M094 (patch status "none in patch10").

| Unit | Source declaration (docstring – end) | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M094.001 | `CyclicCohomology.unitsInvariantSubmodule`, `def` at line 22 (lines 21–24) | `Langlands.NYLL.CyclicCohomology.unitsInvariantSubmodule` (line 27) |

The section context is source lines 17–19: `namespace CyclicCohomology` and
`noncomputable section`. The source file has no `variable`, `universe` or
`open` command before line 24.

## The declaration

```lean
def Langlands.NYLL.CyclicCohomology.unitsInvariantSubmodule
    (K L : Type) [Field K] [Field L] [Algebra K L] :
    Submodule ℤ (Additive Lˣ)
```

The value is `(Rep.ofAlgebraAutOnUnits K L).ρ.invariants`. Here
`Rep.ofAlgebraAutOnUnits K L` is Mathlib's integral representation of the
automorphism group `L ≃ₐ[K] L` (written `Gal(L/K)`) on `Additive Lˣ`, the
units of `L` written additively, with `σ` acting by `x ↦ σ x`. Mathlib's
`Representation.invariants` is the `ℤ`-submodule of vectors fixed by every
group element. So the definition is the group of Galois-invariant units
`(Lˣ)^{Gal(L/K)}`, written additively, inside `Additive Lˣ`. Both fields are
in universe `0`, as in the source, and no finiteness, Galois or
separability hypothesis is assumed.

## Original-to-adapted map and modifications (Worker 5454)

- **Extraction**: only source lines 21–24, with the context of lines 17–19,
  are taken. The private base-unit comparison `invariantUnitToBaseUnit`
  (line 26) and the equivalences that follow it are not part of this unit.
- **Namespace**: `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
  `noncomputable section` is kept.
- **Imports**: the source's two Mathlib imports
  `Mathlib.RepresentationTheory.Invariants` and
  `Mathlib.FieldTheory.Galois.Basic` (lines 7–8) are kept unchanged and in
  order. The source module has no NYLL imports.
- **Declaration**: name, binders, binder kinds, type and body are unchanged.
  The definition is not marked `noncomputable` in the source and is not
  compiled as noncomputable here.
- **Docstrings**: the declaration docstring is the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module holds a copy of the source declaration (lines
  22–24, docstring omitted) inside `noncomputable section`, as in the
  source. A `MetaM` command checks that the original and adapted
  constants have identical universe-parameter lists, identical binder names
  (after erasing hygienic macro scopes) and binder kinds along the whole type
  telescope, and definitionally equal types and values. A further
  `example : @copy = @adapted := rfl` succeeds. Reducibility status and
  noncomputability also agree.
- A second `MetaM` command checks that the elaborated types and values are
  structurally identical (`Expr.equal`), after renaming the copy's constants
  to the adapted ones and erasing hygienic macro scopes from binder names.
  It passed. As a control, a definition that is definitionally equal but
  wraps the value in `id` was rejected by this command.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The copied source code compiles unchanged at the project's pin, so no
  compatibility change was needed.

## Scope

This unit supplies one construction and proves nothing about it. It asserts
no host class-formation, cup-product, Tate, transfer or reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
