# NYLL M020: cyclic factor targets

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

All adapted names use the prefix `Langlands.NYLL.KummerTheory.`, and all
original names the prefix `KummerTheory.`. The source lines are those of the
theorem's binders and statement; the proof is omitted.

| Unit | Original theorem | Source lines | Adapted Prop-valued target |
| --- | --- | --- | --- |
| M020.001 | `finiteCommGroup_exists_jointlyFaithful_cyclic_factors` | 37–43 | `finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement` |
| M020.008 | `extensionSubgroup_isClosed` | 137–140 | `extensionSubgroup_isClosedStatement` |
| M020.009 | `cyclicFactorSubgroup_isClosed` | 149–157 | `cyclicFactorSubgroup_isClosedStatement` |

## Telescopes and statements

Each target takes exactly the source theorem's binders in source order and
returns, as its `Prop` body, exactly the source statement.

- M020.001 (section `FiniteAbelianCyclicFactors`, which has no section
  variables before line 37): `(Q : Type u_1) [CommGroup Q] [Finite Q]`;
  `∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ), (∀ i, 1 < m i) ∧
  ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
  (∀ i, Function.Surjective (f i)) ∧ (⨅ i, MonoidHom.ker (f i)) = ⊥`.
  That is: a finite commutative group `Q` has a finite family, indexed by a
  type in `Type 0`, of surjective homomorphisms onto cyclic groups
  `Multiplicative (ZMod (m i))` of orders `m i > 1` whose kernels meet
  trivially.
- M020.008 (section `ClosedCyclicSubextensions`): the source theorem binds its
  own `{G : Type*} [Group G] [TopologicalSpace G]`, shadowing the section
  variables of line 133, which therefore are not part of its telescope; the
  target does the same. Binders `{G : Type u_2} [Group G] [TopologicalSpace G]
  (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)`; statement
  `IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup)`: `G_L`,
  viewed as a subgroup of `G_K` with the subspace topology, is closed.
- M020.009: binders `{G : Type u_1} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (K L : ClosedSubgroup G)
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
  [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
  {C : Type u_2} [Group C]
  (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C)`; statement
  `IsClosed (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
  Set K.toSubgroup)`: the pull-back to `G_K` of the kernel of `f` is closed.
  The first three binders are the section variables of line 133 and
  `[IsTopologicalGroup G]` is the section variable of line 144. The
  instance `hfinite` is kept as a binder although the statement does not
  mention it.

A `#check` of each target in the Lean service confirmed these telescopes,
including the binder names `hnormal` and `hfinite` and the universe
parameters (`u_1` for M020.001; the single parameter `u_2` for M020.008, the
section variable's `Type*` having taken `u_1`; `u_1` for `G` and `u_2` for
`C` in M020.009).

## Reused declarations

- `Langlands.NYLL.KummerTheory.cyclicFactorSubgroup` (M020.002), from the
  sibling module
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Definitions`.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
  published port of the source's `CyclicCohomology.extensionSubgroup`, used
  with its source spelling through `open CyclicCohomology`. It is
  `L.toSubgroup.subgroupOf K.toSubgroup`.
- Mathlib's `ClosedSubgroup`, which is the source's `ClosedSubgroup`, and
  `ZMod`, `Multiplicative`, `MonoidHom.ker`, `IsClosed`, `IsTopologicalGroup`.

## Modifications

Worker 4918 made only these changes:

1. The namespace `KummerTheory` becomes `Langlands.NYLL.KummerTheory`; the
   source's `open CyclicCohomology` (line 27) now opens
   `Langlands.NYLL.CyclicCohomology`.
2. The source imports `Mathlib.GroupTheory.FiniteAbelian.Basic` and
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerGlobalOperator` (lines 7–8).
   The Mathlib import is kept; the NYLL import is replaced by the modules of
   the two NYLL declarations used, `extensionSubgroup` and
   `cyclicFactorSubgroup`.
3. Each listed `theorem` becomes a `def … : Prop` whose name adds the suffix
   `Statement`; the binders are before the colon and the source statement
   becomes the body. The proofs are omitted.
4. In M020.009 the section instance `variable [IsTopologicalGroup G]`
   (line 144) is written instead as the first explicit binder of the
   definition. Lean includes such an instance of an included variable in a
   theorem's signature, so it is part of the source theorem's telescope, but
   it would not include it in a `def` whose body does not use it. The
   resulting telescope is the source one, in the source order.
5. M020.009, whose statement does not mention `hfinite`, is preceded by
   `set_option linter.unusedVariables false in`; this only silences the
   linter.
6. Each docstring is the source docstring prefixed by `Target M020.xxx:`.
7. The source module docstring (lines 10–23) is replaced by a short
   docstring recording these modifications. The data M020.002 and 003 are
   in the sibling `Definitions` module; the other source declarations are not
   stated here.

No proof is supplied: each target is to be proved separately.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation, cup, transfer, Tate or
reciprocity assertion.
