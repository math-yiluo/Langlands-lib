# NYLL M095.001 and M095.008: the unit norm map and the additive norm subgroup

## Source

The paired Lean file extracts two definitions from Naganori Yamaguchi's
ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean` (206 lines, SHA-256
`a8e71d1ab0523eec0970d399ed9cd92fa5978c7148ff62b075df261c0464feec`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source`. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m073-m096.md`, section
M095 (patch status "none in patch10").

| Unit | Source declaration (docstring – end) | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M095.001 | `CyclicCohomology.unitsNormLinearMap`, `def` at line 32 (lines 31–34) | `Langlands.NYLL.CyclicCohomology.unitsNormLinearMap` (line 38) |
| M095.008 | `CyclicCohomology.additiveNormSubgroup`, `def` at line 119 (lines 118–121) | `Langlands.NYLL.CyclicCohomology.additiveNormSubgroup` (line 43) |

The section context is source lines 22–29: `namespace CyclicCohomology`,
`open LocalFieldTheory`, `open CategoryTheory`, `noncomputable section` and
`universe u`. The source file has no `variable` command. The lemmas between
and after the two units (M095.002–M095.007 and M095.009 onwards) are not part
of this module. The Prop-valued targets for M095.002, M095.007 and M095.009
are in the sibling module `NormImage/Statements`.

## The declarations

```lean
def Langlands.NYLL.CyclicCohomology.unitsNormLinearMap
    (K L : Type) [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)] :
    Additive Lˣ →ₗ[ℤ] Additive Lˣ

def Langlands.NYLL.CyclicCohomology.additiveNormSubgroup.{u}
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    AddSubgroup (Additive Kˣ)
```

- `unitsNormLinearMap K L` is
  `(Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap`. Mathlib's
  `Rep.ofAlgebraAutOnUnits K L` is the integral representation of
  `Gal(L/K) = L ≃ₐ[K] L` on `Additive Lˣ` with `σ` acting by `x ↦ σ x`, and
  `Rep.norm` is the endomorphism `Representation.norm ρ = ∑ σ, ρ σ`. So the
  map sends `x` to `∑_{σ ∈ Gal(L/K)} σ • x`. Written multiplicatively, it
  sends a unit `u` of `L` to `∏_{σ} σ(u)`. The `[Fintype Gal(L/K)]` instance
  is the one needed to form the sum. No Galois, finite-dimensionality or
  separability hypothesis is assumed.
- `additiveNormSubgroup K L` is
  `(localNormSubgroup K L).toAddSubgroup`. Here
  `Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L` (published M093.001)
  is the range of the unit norm `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, the
  norm group `N_{L/K}(Lˣ) ≤ Kˣ`. `Subgroup.toAddSubgroup` is Mathlib's
  order isomorphism from subgroups of `Kˣ` to additive subgroups of
  `Additive Kˣ`. So the definition is the norm group written additively.

## Original-to-adapted map and modifications (Worker 5454)

- **Extraction**: only source lines 31–34 and 118–121 are taken, with the
  context of lines 22–29.
- **Namespace**: `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
  `open LocalFieldTheory` now resolves to `Langlands.NYLL.LocalFieldTheory`,
  where the published `localNormSubgroup` lives. `noncomputable section` and
  `universe u` are kept. `open CategoryTheory` (line 25) is omitted because
  neither construction uses it.
- **Imports**: the source's Mathlib imports
  `Mathlib.FieldTheory.Galois.Basic` and
  `Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90`
  (lines 8–9) are kept. The source's NYLL imports are mapped as follows.
  `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient`
  (line 7) becomes the published M093.001 module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions`.
  `Nyll.GaloisCohomology.Cyclic.TateH0.Invariants` (line 11) becomes this
  port's M094.001 module
  `Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.Invariants.U001.Definitions`,
  so that the sibling targets can use `unitsInvariantSubmodule`.
  `Nyll.GaloisCohomology.Cyclic.TateComparison` (line 10) is not used by
  either construction and is dropped.
- **Declarations**: names, binders, binder kinds, the universe `u`, types and
  bodies are unchanged. Neither definition is noncomputable.
- **Docstrings**: the declaration docstrings are the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module holds copies of the source declarations (lines
  32–34 and 119–121, docstrings omitted) after `open LocalFieldTheory`
  (spelled `open Langlands.NYLL.LocalFieldTheory`), `open CategoryTheory`,
  `noncomputable section` and `universe u`, as in the source. For each definition, a `MetaM` command
  checks that the original and adapted constants have identical
  universe-parameter lists, identical binder names (after erasing hygienic
  macro scopes) and binder kinds along the whole type telescope, and
  definitionally equal types and values. A further
  `example : @copy = @adapted := rfl` succeeds. Reducibility status and
  noncomputability also agree.
- A second `MetaM` command checks that the elaborated types and values are
  structurally identical (`Expr.equal`), after renaming the copy's constants
  to the adapted ones and erasing hygienic macro scopes from binder names.
  Both definitions passed. As a control, a definition that is definitionally
  equal to M094.001 but wraps its value in `id` was rejected by this command.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The copied source code compiles unchanged at the project's pin, so
  no compatibility change was needed.

## Scope

This unit supplies two constructions and proves nothing about them. It
asserts no host class-formation, cup-product, Tate, transfer or reciprocity
result. In particular, it does not identify the norm image with degree-zero
Tate cohomology (source M095.005 `tateUnitsH0IsoInvariantsQuotient` is not
part of this task) or relate `unitsNormLinearMap` to the field norm.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
