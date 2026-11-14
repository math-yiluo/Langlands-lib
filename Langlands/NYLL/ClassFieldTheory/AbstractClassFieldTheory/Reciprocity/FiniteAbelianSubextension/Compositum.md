# NYLL M296.017: the compositum of finite abelian subextensions

Worker 448, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
scaffolding lines 30–52 and the definition `compositum` at lines 212–249
(docstring 212–213, command 214–249). The local lemmas of modification 4 copy
the statements and proofs of four further source theorems:

- `FiniteGaloisSubextension.extensionQuotient_inductionOn`, lines 156–165 of
  `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
  (file SHA-256
  `c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`);
- `FiniteGaloisSubextension.extensionQuotientMk_apply` (M040.012), lines
  109–116 of the same file;
- `FiniteAbelianSubextension.extensionQuotientMk_apply` (M296.011), lines
  110–117 of the M296 source file;
- `KummerTheory.mem_extensionSubgroup_iff` (M022.001), lines 30–38 of
  `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean` (file
  SHA-256 `ca4ad38a7ed46fa029400e2c7718faf0587b4206731c82c8c45d6839b719f54c`).

All files are from the same pinned commit. Registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

## Name map

Adapted names carry the prefix `Langlands.NYLL.ClassFormation.`, original names
the prefix `ClassFormation.`; `FAS` abbreviates `FiniteAbelianSubextension`.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M296.017 | `FAS.compositum` | 212–249 | `FAS.compositum` | def, `FAS K` |

## Telescope and object

The source scaffolding is kept: `noncomputable section` (line 30),
`namespace ClassFormation` (32, prefixed), `open CyclicCohomology` (34, see
modification 3), `universe u` (36), `section GroupOnly` (38) with
`variable {G : Type u} [Group G] [TopologicalSpace G]` (40), and
`namespace FiniteAbelianSubextension` (50) with
`variable {K : ClosedSubgroup G}` (52). No `IsTopologicalGroup G` assumption is
imposed, and the source universe `u` is kept.

**M296.017.** `compositum (L₁ L₂ : FiniteAbelianSubextension K) :
FiniteAbelianSubextension K`, with implicit `{G : Type u}`, `[Group G]`,
`[TopologicalSpace G]` and `{K : ClosedSubgroup G}`, is the structure with

- `toFiniteGaloisExtension :=
  L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension`, the
  published finite Galois compositum
  `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.compositum` (M040),
  whose closed subgroup is `L₁.field ⊓ L₂.field`, i.e. `G_{L₁L₂} = G_{L₁} ∩
  G_{L₂}`; so `(L₁.compositum L₂).field = L₁.field ⊓ L₂.field` holds by `rfl`.
- `commutative`: a proof of
  `IsMulCommutative P.extensionQuotient` for
  `P := L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension`,
  that is commutativity of the actual named finite Galois quotient
  `G_K / (G_{L₁} ∩ G_{L₂})` with its published group structure. The proof is the
  source proof: reduce two quotient elements to classes of `a, b ∈ G_K`, pass
  through `P.extensionQuotientMulEquiv` to the raw quotient, and show that the
  commutator-type element `(a * b)⁻¹ * (b * a)` lies in `G_{L₁}` and in
  `G_{L₂}`, using commutativity of `L₁.extensionQuotient` and
  `L₂.extensionQuotient`.

## Reused Library declarations

- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` (M296.001) with
  `field`, `below`, `normal` (M296.002–.004), `extensionQuotientMulEquiv`
  (M296.009) and `extensionQuotientMk` (M296.010) from the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`.
- `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.compositum` (M040),
  with the finite Galois `field`, `below`, `normal`, `extensionQuotient`,
  `extensionQuotientMulEquiv` and `extensionQuotientMk`, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
  (imported through the M296 data module). This is the source's own boundary;
  it is not duplicated.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (an abbreviation for
  `L.toSubgroup.subgroupOf K.toSubgroup`), used under its own name through
  `open CyclicCohomology`.
- Mathlib's `IsMulCommutative`, `Quotient.inductionOn'`, `QuotientGroup.leftRel`,
  `QuotientGroup.mk`, `QuotientGroup.eq`, `MulEquiv.injective` and `map_mul`.

## Modifications

Worker 448 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The source imports
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`,
   `Mathlib.Algebra.Group.Subgroup.Pointwise` and
   `Mathlib.Topology.Algebra.Group.Pointwise` are replaced by the single published
   module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`.
   The definition does not use the order instance M296.014 or the base change
   construction, so neither is imported.
3. `open CyclicCohomology KummerTheory` (line 34) becomes `open CyclicCohomology`:
   the only `KummerTheory` name the source uses here, `mem_extensionSubgroup_iff`,
   is replaced by a local lemma (modification 4), and that namespace is not
   imported.
4. The proof of the `commutative` field uses four source theorems that the
   Library does not prove at the base commit (the last three are stated there
   only as the targets
   `FiniteGaloisSubextension.extensionQuotientMk_applyStatement`,
   `FiniteAbelianSubextension.extensionQuotientMk_applyStatement` and
   `Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iffStatement`; the first is
   not stated). After the three source `let` lines (221–223), the proof
   introduces local `have`s with the source statements, specialised as used,
   and the source proofs:
   - `P_extensionQuotient_inductionOn : ∀ {motive : P.extensionQuotient → Prop}
     (q : P.extensionQuotient), (∀ k : K.toSubgroup, motive
     (P.extensionQuotientMk k)) → motive q`, proved by the source term
     `@Quotient.inductionOn' K.toSubgroup (QuotientGroup.leftRel
     (extensionSubgroup K P.field P.below)) motive q mk` (the source wraps it in
     `by exact`);
   - `P_extensionQuotientMk_apply`, `L₁_extensionQuotientMk_apply` and
     `L₂_extensionQuotientMk_apply : ∀ k : K.toSubgroup,
     X.extensionQuotientMulEquiv (X.extensionQuotientMk k) = (QuotientGroup.mk k :
     K.toSubgroup ⧸ extensionSubgroup K X.field X.below)` for `X = P, L₁, L₂`,
     each proved by `rfl` as in the source;
   - `mem_extensionSubgroup_iff : ∀ (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤
     K.toSubgroup) (k : K.toSubgroup), k ∈ extensionSubgroup (G := G) K L hLK ↔
     (k : G) ∈ L`, proved by `Iff.rfl` as in the source (here `G` is the section
     variable rather than a fresh `Type*`).

   The source calls `P.extensionQuotient_inductionOn`, `P.extensionQuotientMk_apply`,
   `L₁.extensionQuotientMk_apply` and `L₂.extensionQuotientMk_apply` become
   `P_extensionQuotient_inductionOn`, `P_extensionQuotientMk_apply`,
   `L₁_extensionQuotientMk_apply` and `L₂_extensionQuotientMk_apply`;
   `mem_extensionSubgroup_iff` keeps its name. Every other proof line (224–249)
   is unchanged. A comment marks the local copies. Only a proof field changes;
   the data field `toFiniteGaloisExtension` is the source one.
5. The source module docstring (lines 11–26) is replaced by a short docstring
   recording these modifications.
6. Only `compositum` (lines 212–249) is ported. The order M296.014 is in the
   sibling `Order` module and the targets M296.015 and M296.018–.020 in
   `OrderStatements`; base change, intersection and the other source
   declarations belong to other tasks. As in the source, the
   `noncomputable section` is left open to the end of the file.

The docstring, binders and the data field are otherwise unchanged.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings. A
private harness checked, also without errors or warnings, that
`(L₁.compositum L₂).toFiniteGaloisExtension` and `(L₁.compositum L₂).field`
are `L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension` and
`L₁.field ⊓ L₂.field` by `rfl`; that the source proofs (`rfl`, `rfl`,
`Iff.rfl`) prove the published targets
`FiniteGaloisSubextension.extensionQuotientMk_applyStatement`,
`FiniteAbelianSubextension.extensionQuotientMk_applyStatement` and
`KummerTheory.mem_extensionSubgroup_iffStatement`, the last of which equals the
type of the local `mem_extensionSubgroup_iff` by `rfl`; and that the source
proofs of `le_compositum_left`, `le_compositum_right` and `compositum_le`
prove the sibling targets. These checks establish compilation and source
correspondence only; independent review is still required.
