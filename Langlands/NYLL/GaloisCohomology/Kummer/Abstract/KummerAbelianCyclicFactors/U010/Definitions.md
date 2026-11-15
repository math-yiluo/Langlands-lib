# NYLL M020: the closed cyclic-factor intermediate subgroup

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean`
(file SHA-256 `abedaf33dffa23e93392885b9c29e77ead8a9452ee32d9100614f6f0ac731033`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M020.010 | `KummerTheory.closedCyclicFactorSubgroup` | 164–182 | `Langlands.NYLL.KummerTheory.closedCyclicFactorSubgroup` | def |

The source lines include the docstring.

## Telescope and object

The surrounding source scaffolding is kept: `namespace KummerTheory`
(line 25), `open CyclicCohomology` (27), `noncomputable section` (31),
`section ClosedCyclicSubextensions` (131) with its section variables
`variable {G : Type*} [Group G] [TopologicalSpace G]` (133) and
`variable [IsTopologicalGroup G]` (144).

`closedCyclicFactorSubgroup` has the telescope
`{G : Type u_1} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
(K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
[hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
[hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
{C : Type u_2} [Group C]
(f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C)`
and returns a `ClosedSubgroup G`. Both section instances are part of the
telescope, because the body uses them. Its two fields are exactly the source
ones:

- `toSubgroup` is
  `(cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f).map K.toSubgroup.subtype`:
  the image in `G` of the subgroup of `G_K` obtained by pulling back the
  kernel of the factor `f` of `G_K / G_L`. Here `G_L` inside `G_K` is
  `extensionSubgroup K L hLK`.
- `isClosed'` is the source tactic proof. It rewrites the carrier as the
  image of that pulled-back subgroup under `Subtype.val`, and applies
  `K.isClosed'.isClosedMap_subtype_val` (Mathlib: the inclusion of a closed
  subset is a closed map) to the published proof
  `cyclicFactorSubgroup_isClosed K L hLK f` of M020.009 that the pulled-back
  subgroup is closed in `G_K`. That proof has the type
  `cyclicFactorSubgroup_isClosedStatement K L hLK f`, which unfolds to the
  source statement `IsClosed (cyclicFactorSubgroup … f : Set K.toSubgroup)`.

A `#check` in the Lean service confirmed this telescope, with the binder
names `hnormal` and `hfinite` and the universe parameters `u_1` (of `G`)
and `u_2` (of `C`).

## Reused declarations

- `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup` (M020.002) and its
  normality instance (M020.003), from
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Definitions`.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
  published port of the source's `CyclicCohomology.extensionSubgroup`
  (`L.toSubgroup.subgroupOf K.toSubgroup`), used with its source spelling
  through `open CyclicCohomology`.
- The published proof `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup_isClosed`
  of the target `cyclicFactorSubgroup_isClosedStatement` (M020.009), from
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U009.Proofs`.
- Mathlib's `ClosedSubgroup`, which is the source's `ClosedSubgroup`, and
  `Subgroup.map`, `Subgroup.subtype`, `IsClosed.isClosedMap_subtype_val`.

## Modifications

Worker 4918 made only these changes:

1. The namespace `KummerTheory` becomes `Langlands.NYLL.KummerTheory`; the
   source's `open CyclicCohomology` (line 27) now opens
   `Langlands.NYLL.CyclicCohomology`.
2. The source imports `Mathlib.GroupTheory.FiniteAbelian.Basic` and
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerGlobalOperator` (lines 7–8).
   They are replaced by the single import of the published M020.009 proof
   module, which brings in M020.002, `extensionSubgroup`, the M020.009 target
   and Mathlib.
3. The source module docstring (lines 10–23) is replaced by a short
   docstring recording these modifications. The other source declarations
   are not in this module.

The definition, its binders, docstring and body are otherwise unchanged; the
proof of M020.009 that the body uses is imported, not inlined.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation, cup, transfer, Tate or
reciprocity assertion.
