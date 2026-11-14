# NYLL M116.002 and M116.004: equivariant homomorphisms as representation morphisms and their short complex

## Source

The paired Lean file extracts two definitions from Naganori Yamaguchi's
ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean`
(362 lines, SHA-256
`f483093db92c9aea3553e6378269c66890d414c28ede02630f5ffddf9eee4ca2`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source`. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M116 (patch status "none in patch10").

| Unit | Source declaration (docstring – end) | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M116.002 | `CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom`, `def` at line 34 (lines 32–43) | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom` (line 41) |
| M116.004 | `CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex`, `def` at line 54 (lines 52–65) | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex` (line 54) |

The section context is source lines 12–30: `open CategoryTheory`,
`namespace CyclicCohomology.ProfiniteCohomology.Herbrand`,
`noncomputable section`, `universe u w`, the private theorem
`repExact_of_hom_exact` (M116.001, lines 20–25) and the `variable` commands
of lines 27–30. Neither definition uses M116.001. The theorem
`equivariantRepHom_apply` (M116.003, lines 45–50) lies between the two units
and is not part of this task. The Prop-valued target for M116.005 is in the
sibling module `TateComparison/Statements`.

## The declarations

The section variables of lines 27–30 are kept verbatim as `variable`
commands (paired Lean lines 34–37). As in the source, Lean includes in each
definition only the section variables that the definition uses, so neither
takes `[Fintype G]`, and `equivariantRepHom` does not take `C`. The
elaborated signatures, identical in source and port, are:

```lean
def Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom
    {G A B : Type} [Group G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.ofMulDistribMulAction G A ⟶ Rep.ofMulDistribMulAction G B

def Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex
    {G A B C : Type} [Group G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (Rep ℤ G)
```

- `Rep.ofMulDistribMulAction G A` is Mathlib's integral representation of
  `G` on `Additive A`, with `g` acting by `g • ·`. `equivariantRepHom f hf`
  is the morphism of representations whose underlying `ℤ`-linear map is the
  additive form `MonoidHom.toAdditive f : Additive A → Additive B` of `f`.
  Its `G`-equivariance is proved from `hf`, by the source's tactic proof.
- `equivariantShortComplex i j hi hj hker` is the short complex
  `Additive A → Additive B → Additive C` in `Rep ℤ G` formed by
  `equivariantRepHom i hi` and `equivariantRepHom j hj`. The proof field
  that the composite is zero uses the backward direction of `hker` (the
  composite `j ∘ i` is trivial), by the source's tactic proof. Nothing here
  asserts exactness.

## Original-to-adapted map and modifications (Worker 5454)

- **Extraction**: only source lines 32–43 and 52–65 are taken, with the
  context of lines 12–18 and 27–30.
- **Namespace**: `CyclicCohomology.ProfiniteCohomology.Herbrand` becomes
  `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.
  `open CategoryTheory` and `noncomputable section` are kept.
- **Universes**: `universe u w` (line 18) is used in the source only by the
  private theorem M116.001, which is not part of this unit. It is omitted.
  Both definitions live in universe `0`, as in the source.
- **Imports**: the source imports only NYLL modules,
  `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic` and
  `Nyll.GaloisCohomology.Cyclic.TateComparison` (lines 7–8). Neither
  construction uses a declaration from them. They are replaced by the two
  Mathlib modules that supply what is used:
  `Mathlib.RepresentationTheory.Rep.Basic` (`Rep.ofMulDistribMulAction`,
  `Rep.ofHom`, `Rep.hom_ext`) and `Mathlib.Algebra.Homology.ShortComplex.Basic`
  (`ShortComplex`).
- **Declarations**: names, binders, binder kinds, types and bodies,
  including the tactic proofs of the two proof fields, are unchanged.
- **Docstrings**: the declaration docstrings are the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module holds a copy of source lines 27–43 and 52–65 (the
  `variable` commands and both definitions, docstrings omitted), after
  `open CategoryTheory` and `noncomputable section` as in the source. For both definitions, a `MetaM` command checks that
  the original and adapted constants have identical universe-parameter lists,
  identical binder names (after erasing hygienic macro scopes) and binder
  kinds along the whole type telescope (10 binders for `equivariantRepHom`,
  16 for `equivariantShortComplex`), and definitionally equal types and
  values. A further `example : @copy = @adapted := rfl` succeeds for each.
  Reducibility status and noncomputability also agree.
- A second `MetaM` command checks that the elaborated types and values are
  structurally identical (`Expr.equal`), after renaming the copy's constants
  to the adapted ones and erasing hygienic macro scopes from binder names.
  Both definitions passed, so the proof terms inside them are also the
  source's. As a control, a definitionally equal but syntactically different
  definition was rejected by this command.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The copied source code compiles unchanged at the project's pin, so no
  compatibility change was needed.

## Scope

This unit supplies two constructions and proves nothing about them. It
asserts no host class-formation, cup-product, Tate, transfer or reciprocity
result, and no Herbrand-quotient comparison (M116.009 and M116.012 are not
part of this task).

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
