# NYLL M020: the closed cyclic-factor subgroup lies below the base

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

| Unit | Original theorem | Source lines | Adapted Prop-valued target |
| --- | --- | --- | --- |
| M020.011 | `KummerTheory.closedCyclicFactorSubgroup_le_base` | 184–192 | `Langlands.NYLL.KummerTheory.closedCyclicFactorSubgroup_le_baseStatement` |

The source lines are those of the docstring, binders and statement; the proof
(lines 193–194) is omitted.

## Telescope and statement

The surrounding source scaffolding is kept: `namespace KummerTheory`
(line 25), `open CyclicCohomology` (27), `noncomputable section` (31),
`section ClosedCyclicSubextensions` (131) with its section variables
`variable {G : Type*} [Group G] [TopologicalSpace G]` (133) and
`variable [IsTopologicalGroup G]` (144).

The target takes exactly the source theorem's binders in source order,
`{G : Type u_1} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
(K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
[hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
[hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
{C : Type u_2} [Group C]
(f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C)`,
and returns, as its `Prop` body, exactly the source statement
`(closedCyclicFactorSubgroup K L hLK f).toSubgroup ≤ K.toSubgroup`: the
closed cyclic-factor intermediate subgroup attached to `f` lies in `G_K`.
Both section instances are part of the telescope, because
`closedCyclicFactorSubgroup` needs them; `hnormal` and `hfinite` are
used as instance arguments of `closedCyclicFactorSubgroup`.

A `#check` in the Lean service confirmed this telescope, with the binder
names `hnormal` and `hfinite` and the universe parameters `u_1` (of `G`)
and `u_2` (of `C`).

## Reused declarations

- `Langlands.NYLL.KummerTheory.closedCyclicFactorSubgroup` (M020.010), from
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U010.Definitions`.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), used with
  its source spelling through `open CyclicCohomology`.
- Mathlib's `ClosedSubgroup` and `IsTopologicalGroup`.

## Modifications

Worker 4918 made only these changes:

1. The namespace `KummerTheory` becomes `Langlands.NYLL.KummerTheory`; the
   source's `open CyclicCohomology` (line 27) now opens
   `Langlands.NYLL.CyclicCohomology`.
2. The source imports (lines 7–8) are replaced by the single import of the
   published M020.010 module.
3. The `theorem` becomes a `def … : Prop` whose name adds the suffix
   `Statement`; the binders are before the colon and the source statement
   becomes the body. The proof is omitted.
4. The docstring is the source docstring prefixed by `Target M020.011:`.
5. The source module docstring (lines 10–23) is replaced by a short
   docstring recording these modifications. The other source declarations
   are not in this module.

No proof is supplied: the target is to be proved separately.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation, cup, transfer, Tate or
reciprocity assertion.
