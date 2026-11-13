# NYLL M023.001: ambient fixed additive subgroup of a representation

The paired Lean file extracts
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`
from Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean`,
M023.001, lines 30–44: the section variables at line 30, the docstring at
lines 32–33 and the definition at lines 34–44. The rest of the enclosing context
is `namespace KummerTheory` (line 22), `open CyclicCohomology` (line 24) and
`noncomputable section` (line 28). The source file SHA-256 is
`6778a3be3b28518c10a0288dd21befed505cf6bed556590eab1f4dba82f166b8`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project notes.

## The definition

For a group `G` with a topology, an integral representation `A` of `G` and a
closed subgroup `H` of `G`, the definition gives the additive subgroup of the
underlying module `A.V` whose elements are fixed by every element of `H`:

```lean
def Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup
    {G : Langlands.NYLL.IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (H : ClosedSubgroup G) : AddSubgroup A.V
```

Its carrier is `{a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}`. This is the ambient
version of the invariants `A^H`. It is an `AddSubgroup` of the whole module
`A.V`, not a separate module or representation. The source uses it to describe
fixed modules such as `A_K` and `A_L` inside one ambient coefficient module.

The complete telescope is the source's section telescope: implicit
`G : IntegralRepGroupType`, which is `Type 0`, then `[Group G]` and
`[TopologicalSpace G]`, then explicit `A : Rep ℤ G` and `H : ClosedSubgroup G`.
`IntegralRepGroupType` resolves to the published
`Langlands.NYLL.IntegralRepGroupType` (an abbreviation for `Type 0`). The group's
universe stays fixed at zero. The universe of the carrier of `A` is left free,
as in the source, where `Rep ℤ G` is written without a universe annotation. So
the declaration has one universe parameter, `u_1`. `Rep` and `ClosedSubgroup`
are Mathlib's. The topology enters only through `ClosedSubgroup G`. The closedness
field `isClosed'` of `H` is never used, and the definition adds no continuity,
compactness, profiniteness or discreteness assumptions.

The construction is the source's, character for character. It is a tactic block
`by exact { ... }` that builds an `AddSubgroup` structure with these fields:

- `carrier := {a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}`;
- `zero_mem' := fun h => map_zero (A.ρ h.1)`, since each `A.ρ g` is linear;
- `add_mem'` by `rw [map_add, ha h, hb h]`;
- `neg_mem'` by `rw [map_neg, ha h]`.

The definition is inside the source's `noncomputable section`, which is kept.
It depends only on the axioms `propext` and `Quot.sound`.

## Adaptations

Worker 232 made these changes:

1. The namespace is now `Langlands.NYLL.KummerTheory` instead of `KummerTheory`.
2. The source imports are
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly`,
   `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` and
   `Nyll.GaloisCohomology.Cyclic.NormKernelVanishing`. They are replaced by
   `Mathlib.RepresentationTheory.Rep.Basic` (for `Rep`),
   `Mathlib.Topology.Algebra.Group.ClosedSubgroup` (for `ClosedSubgroup`) and
   the published `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`.
   This construction uses nothing from the two dropped NYLL modules. A
   successful focused check of the module with only these imports confirms
   that.
3. `open CyclicCohomology` is dropped. This declaration uses no name from that
   namespace, and the namespace is not imported here.
4. The module docstring is replaced by a short description and a modification
   notice. The source's later M023 declarations are left out.

The declaration docstring, binder names, telescope, construction and
`noncomputable section` are unchanged. The definition adds no global instances.

## Verification

Checks were run in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean
v4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; the source pins
Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`). The focused module compiles
with no errors or warnings. Declaration inspection reports a definition with
level parameter `u_1` and axioms `propext` and `Quot.sound`. A private probe ran
three further checks:

- `#print` shows the elaborated type
  `{G : IntegralRepGroupType} → [Group G] → [TopologicalSpace G] →
  (A : Rep ℤ G) → ClosedSubgroup G → AddSubgroup ↑A` and the structure value
  above.
- The term elaborates against the expected type for an arbitrary carrier
  universe `Rep.{u} ℤ G`.
- Membership `a ∈ ambientFixedAddSubgroup A H ↔ ∀ h : H.toSubgroup, A.ρ h.1 a = a`
  holds by `Iff.rfl`, and the coerced set equals the source carrier by `rfl`.
  These are the definitional facts that source M023.002 relies on.

## Scope

This contribution supplies only the subgroup data. The membership theorem
M023.002, `kummerDeltaAddSubgroup` (M023.003), `kummerRadicalAddSubgroup`
(M023.004) and the later radical and fixing-subgroup results M023.005–007 are
separate units. It asserts no class-formation, cup-product, Tate, transfer or
cohomological reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header are kept verbatim:
copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by
OpenAI Codex). The license and notice are kept at
[`licenses/NYLL/LICENSE`](../../../../../../../licenses/NYLL/LICENSE)
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [`licenses/NYLL/NOTICE`](../../../../../../../licenses/NYLL/NOTICE)
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
The original NOTICE has no entry specific to this source file.
