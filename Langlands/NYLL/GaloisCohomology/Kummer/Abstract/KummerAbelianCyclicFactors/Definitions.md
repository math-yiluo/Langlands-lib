# NYLL M020: pulled-back cyclic factor subgroups

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
| M020.002 | `KummerTheory.cyclicFactorSubgroup` | 66–68 | `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup` | def |
| M020.003 | `KummerTheory.cyclicFactorSubgroup_normal` | 70–73 | `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup_normal` | instance |

The source lines include each declaration's docstring.

## Telescope and objects

The surrounding source scaffolding is kept: `namespace KummerTheory`
(line 25), `noncomputable section` (31), `section FiniteAbelianCyclicFactors`
(33) and `section Pullback` (61) with the section variables (63–64)

```
variable {P C : Type*} [Group P] [Group C]
  (H : Subgroup P) [H.Normal]
```

- `cyclicFactorSubgroup` has the telescope `{P : Type u_1} {C : Type u_2}
  [Group P] [Group C] (H : Subgroup P) [H.Normal] (f : (P ⧸ H) →* C)` and
  returns a `Subgroup P`. Its body is exactly the source body
  `MonoidHom.ker (f.comp (QuotientGroup.mk' H))`: the kernel of the
  composite `P → P ⧸ H → C`, that is, the pull-back to `P` of the kernel of
  the factor `f` of the quotient.
- `cyclicFactorSubgroup_normal` has the same telescope and the type
  `(cyclicFactorSubgroup H f).Normal`. Its body is exactly the source term
  `MonoidHom.normal_ker _` (Mathlib: the kernel of a homomorphism is normal).

A `#check` in the Lean service confirmed both telescopes with the two universe
parameters `u_1` (of `P`) and `u_2` (of `C`), and that instance search now
finds `(cyclicFactorSubgroup H f).Normal`.

As in the source, the instance is an ordinary (global, unscoped) instance.
It concerns only the new definition `cyclicFactorSubgroup`, which is not
reducible, so it does not overlap any Mathlib or Library instance.

## Reused declarations

Only Mathlib is used: `Subgroup`, `Subgroup.Normal`, the quotient group
`P ⧸ H`, `QuotientGroup.mk'`, `MonoidHom.comp`, `MonoidHom.ker` and
`MonoidHom.normal_ker`.

## Modifications

Worker 4918 made only these changes:

1. The namespace `KummerTheory` becomes `Langlands.NYLL.KummerTheory`.
2. The source imports `Mathlib.GroupTheory.FiniteAbelian.Basic` and
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerGlobalOperator` (lines 7–8).
   Only the Mathlib import is kept, since these two declarations use nothing
   from the NYLL module.
3. `open CyclicCohomology` (line 27) is dropped: these two declarations use
   nothing from that namespace, and it is not imported here.
4. The source module docstring (lines 10–23) is replaced by a short
   docstring recording these modifications. The other source declarations
   are not in this module: the theorem targets M020.001, 008 and 009 are
   stated in a separate module, and the remaining source declarations belong
   to other units.

The declarations, binders, docstrings and bodies are otherwise unchanged.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation, cup, transfer, Tate or
reciprocity assertion.
