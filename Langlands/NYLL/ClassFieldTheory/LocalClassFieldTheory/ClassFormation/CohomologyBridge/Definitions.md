# NYLL M114 data: fixed units as invariants, the restricted coboundary `ρ(g) - 1` and three private quotient helpers

## Source

The paired Lean file extracts five definitions from Naganori Yamaguchi's
ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`
(491 lines, SHA-256
`97f7d1f21d8bf5cb2fa787caba600d6820c4be4d91e00d1ebe4f89b89f29830b`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source`. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M114 (patch status "none in patch10").

| Unit | Source declaration (docstring – end) | Adapted declaration (paired Lean line) |
| --- | --- | --- |
| M114.002 | `LocalClassFieldTheory.additiveFixedUnitsEquivInvariants`, `def` at line 62 (lines 60–73) | `Langlands.NYLL.LocalClassFieldTheory.additiveFixedUnitsEquivInvariants` (line 76) |
| M114.004 | `LocalClassFieldTheory.additiveHomToMultiplicativeHom`, `private def` at line 87 (lines 85–90) | `Langlands.NYLL.PortInternal.M114.d004` (line 37) |
| M114.005 | `LocalClassFieldTheory.multiplicativeQuotientGroup`, `@[implicit_reducible] private def` at line 96 (lines 92–99) | `Langlands.NYLL.PortInternal.M114.d005` (line 46, attribute line 45) |
| M114.006 | `LocalClassFieldTheory.kernelOfAdditiveQuotientHom`, `private def` at line 103 (lines 101–107) | `Langlands.NYLL.PortInternal.M114.d006` (line 53) |
| M114.019 | `LocalClassFieldTheory.unitsRhoSubToNormKerLinearMap`, `def` at line 292 (lines 290–307) | `Langlands.NYLL.LocalClassFieldTheory.unitsRhoSubToNormKerLinearMap` (line 91) |

The section context is source lines 22–33: `namespace LocalClassFieldTheory`,
`open CyclicCohomology`, `noncomputable section`, `open scoped BigOperators`,
`open CyclicCohomology.ProfiniteCohomology.Herbrand`, `open CategoryTheory`
and `variable (K L : Type) [Field K] [Field L] [Algebra K L]` (line 33). The
file has no other `variable` or `universe` command. The theorems M114.001 and
M114.017 have Prop-valued targets in the sibling module
`CohomologyBridge/Statements`. The other source declarations, including the
private M114.003 `additiveEquivToQuotientHom` (lines 75–83) mentioned in the
docstring of M114.004, are not part of this task.

## The declarations

```lean
def Langlands.NYLL.PortInternal.M114.d004
    {G B : Type} [Group G] [AddCommGroup B]
    (f : Additive G →+ B) : G →* Multiplicative B

@[implicit_reducible]
def Langlands.NYLL.PortInternal.M114.d005
    {M : Type} [AddCommGroup M] (N : Submodule ℤ M) :
    Group (Multiplicative (M ⧸ N))

def Langlands.NYLL.PortInternal.M114.d006
    {G M : Type} [Group G] [AddCommGroup M]
    (N : Submodule ℤ M) (f : G →* Multiplicative (M ⧸ N)) : Subgroup G

def Langlands.NYLL.LocalClassFieldTheory.additiveFixedUnitsEquivInvariants
    (K L : Type) [Field K] [Field L] [Algebra K L] :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) ≃+ unitsInvariantSubmodule K L

def Langlands.NYLL.LocalClassFieldTheory.unitsRhoSubToNormKerLinearMap
    (K L : Type) [Field K] [Field L] [Algebra K L] [Fintype (Gal(L/K))]
    (g : Gal(L/K)) :
    Additive Lˣ →ₗ[ℤ] LinearMap.ker (unitsNormLinearMap K L)
```

- `d004 f` is `AddMonoidHom.toMultiplicativeRight f`, Mathlib's
  multiplicative form `G →* Multiplicative B` of an additive homomorphism
  `Additive G →+ B`.
- `d005 N` is `Multiplicative.group`, the group structure on
  `Multiplicative (M ⧸ N)` coming from the additive group `M ⧸ N`. It keeps
  the source's `@[implicit_reducible]` attribute.
- `d006 N f` is `MonoidHom.ker f`, the kernel of `f`, formed with the
  `MulOneClass` structure `(d005 N).toMulOneClass` on the codomain.
- `additiveFixedUnitsEquivInvariants K L` is the additive group isomorphism
  between the subgroup of units of `L` fixed by every `σ ∈ Gal(L/K)`
  (`fixedSubgroup`, published M113.003), written additively, and the
  invariant submodule `unitsInvariantSubmodule K L` (M094.001). Both maps are
  the identity on underlying units; the proof fields are the source's
  (`left_inv`, `right_inv` and `map_add'` by `rfl`).
- `unitsRhoSubToNormKerLinearMap K L g` is the `ℤ`-linear map
  `ρ(g) - id : Additive Lˣ → Additive Lˣ` of the unit representation
  `Rep.ofAlgebraAutOnUnits K L`, with codomain restricted to the kernel of
  `unitsNormLinearMap K L` (M095.001). Multiplicatively it sends `x` to
  `g(x)/x`. The membership proof is the source's: it uses
  `Representation.norm_self_apply`, i.e. `N(ρ(g)x) = N(x)`.

## Original-to-adapted map and modifications (Worker 5454)

- **Extraction**: only source lines 60–73, 85–107 and 290–307 are taken,
  with the context of lines 22–33.
- **Public names**: `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`. The source's `open` commands are
  kept; `CyclicCohomology` and
  `CyclicCohomology.ProfiniteCohomology.Herbrand` now resolve to the
  `Langlands.NYLL` namespaces. `noncomputable section` and the `variable`
  command of line 33 are kept.
- **Private definitions**: as required by the task and the inventory, the
  private M114.004, M114.005 and M114.006 become public definitions
  `Langlands.NYLL.PortInternal.M114.d004`, `d005` and `d006`. Inside the body
  of M114.006 the call `multiplicativeQuotientGroup N` becomes `d005 N`. These
  three definitions are placed in their own namespace block before the
  `LocalClassFieldTheory` block, outside its `noncomputable section` and
  `variable` command. In the source they do not use the section variables
  `K` and `L`, so their elaborated telescopes are unchanged. They are
  computable in both the source and the port. Their docstrings are the
  source's, including the reference to `additiveEquivToQuotientHom` in the
  docstring of M114.004.
- **Imports**: the source's Mathlib import `Mathlib.SetTheory.Cardinal.Finite`
  (line 7) is kept. Of its NYLL imports, `Nyll.GaloisCohomology.Cyclic.TateH0.NormImage`
  (line 10) becomes this port's M095 data module
  `Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions`
  (`unitsNormLinearMap`, and `unitsInvariantSubmodule` through its M094
  import), and `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic`
  (line 11) becomes the published M113 data module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`
  (`fixedSubgroup`). `Nyll.GaloisCohomology.Cyclic.GaloisCohomology` (line 8)
  and `Nyll.GaloisCohomology.Cyclic.NormKernelVanishing` (line 9) are not used
  by these five definitions and are dropped.
- **Declarations**: binders, binder kinds, types, bodies, proof fields and the
  attribute are unchanged.
- **Docstrings**: the declaration docstrings are the source's. The module
  docstring is replaced by a modification notice.

## Verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings.
- A private audit module holds a copy of the five source declarations
  (docstrings omitted, and the three private definitions declared without
  `private`) after the source's `open` commands, `noncomputable section` and
  the `variable` command of line 33, as in the source. For each definition, a
  `MetaM` command checks that the original and adapted constants have
  identical universe-parameter lists, identical binder names (after erasing
  hygienic macro scopes) and binder kinds along the whole type telescope, and
  definitionally equal types and values. A further
  `example : @copy = @adapted := rfl` succeeds for each. Reducibility status
  (`implicitReducible` for `d005` and its copy) and noncomputability also
  agree.
- A second `MetaM` command checks that the elaborated types and values are
  structurally identical (`Expr.equal`), after renaming the copy's constants
  to the adapted ones (for M114.006, the copy of M114.005 to `d005`) and
  erasing hygienic macro scopes from binder names. All five definitions
  passed, so the proof terms inside them are also the source's. As a
  control, a definitionally equal but syntactically different definition was
  rejected by this command.
- The source was written against Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, as recorded in the attribution
  supplement. The copied source code compiles unchanged at the project's pin,
  so no compatibility change was needed.

## Scope

This unit supplies five constructions and proves nothing about them. It
asserts no host class-formation, cup-product, Tate, transfer or reciprocity
result, and none of the Herbrand-quotient comparisons of the source file
(M114.014–M114.016 and M114.024–M114.028 are not part of this task).

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
