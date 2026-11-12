# Profinite invariant rings: normality on maximal residue fields

This module states the source unit M242.001 from Naganori Yamaguchi's
*ClassFieldTheory (NYLL)*, commit `fbd320cd8b1b06487c58227e92eb135794267709`:
the theorem `RamificationTheory.Ideal.Quotient.normal_of_profinite` in
[`Nyll/ValuedFieldTheory/Ramification/ProfiniteInvariant.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/ProfiniteInvariant.lean#L26-L101),
lines 26–101, with the theorem at line 45. The declaration
`Langlands.NYLL.RamificationTheory.Ideal.Quotient.normal_of_profiniteStatement`
is a definition returning `Prop`. It proves nothing; a proof of this exact
closed proposition belongs to a separate unit after the statement is published.

## Complete proposition

The imports are the two original imports, `Mathlib.FieldTheory.Galois.Profinite`
and `Mathlib.RingTheory.Invariant.Profinite`. The module declares
`universe u v w`. Inside `Langlands.NYLL.RamificationTheory.Ideal.Quotient`,
after `attribute [local instance] Ideal.Quotient.field`, the entire
declaration is:

```lean
def normal_of_profiniteStatement : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type w} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
    [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P],
    Normal (A ⧸ P) (B ⧸ Q)
```

The declaration has no ordinary parameters. Its only parameters are the three
independent universe levels `u`, `v`, `w`, the universes of `A`, `B` and `G`.

## Mathematical meaning

Let `A` and `B` be commutative rings and let `B` be an `A`-algebra. The
algebra map need not be injective. Let `G` be a group acting on `B` by ring
automorphisms (`MulSemiringAction G B`). The action commutes with the
`A`-scalar action (`SMulCommClass G A B`), so `G` acts by `A`-algebra
automorphisms. `G` carries a topology making it a compact, totally
disconnected topological group. `B` carries the discrete topology, and the
action map `G × B → B` is continuous. `Algebra.IsInvariant A B G` says that
every `G`-fixed element of `B` lies in the image of `A`.

Let `P` be a maximal ideal of `A` and `Q` a maximal ideal of `B` lying over
`P`, i.e. `P` is the preimage of `Q` under the algebra map. The proposition
asserts that the residue field extension `(B ⧸ Q) / (A ⧸ P)` is normal in
Mathlib's sense: it is algebraic, and the minimal polynomial over `A ⧸ P` of
every element of `B ⧸ Q` splits in `B ⧸ Q`.

The structures in the conclusion are the following; this was confirmed by
printing the elaborated definition with explicit instances.

- The field structures on `A ⧸ P` and `B ⧸ Q` are `Ideal.Quotient.field`,
  applied to the maximality instances of `P` and `Q`. This is the source's
  local instance, kept local here (see the map below).
- The algebra structure is Mathlib's `Ideal.Quotient.algebraOfLiesOver`, built
  from `Q.LiesOver P`. It sends the class of `a` to the class of the image of
  `a` in `B`.

## Original-to-adapted map

The whole source file was read (105 lines). Its SHA-256 is
`16a8b3a7e109a3a3ac55f3ef4133488713c3d049d9f095b79415d71153ae213e`, the value
recorded for M242 in the
[port inventory](../../../../../notes/reuse/nyll-public-port/m241-m258.md#m242).

| Original lines | Original content | Adapted form |
| --- | --- | --- |
| 1–5 | Copyright and author header | Kept verbatim. A modification note follows it in the same comment. |
| 7–8 | `import Mathlib.FieldTheory.Galois.Profinite`, `import Mathlib.RingTheory.Invariant.Profinite` | Unchanged. |
| 10–18 | Module docstring “normality on prime residue fields” | Replaced by a short docstring for the statement. It says “maximal”, because the theorem requires both ideals to be maximal (see below). |
| 20, 34 | `namespace RamificationTheory`, then `namespace Ideal.Quotient` | One combined `namespace Langlands.NYLL.RamificationTheory.Ideal.Quotient`. |
| 24 | `noncomputable section` | Omitted. A `Prop` has no computational content. |
| 26 | `open scoped Pointwise` | Omitted. The statement uses no pointwise notation. |
| 28 | `variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]` | First binders of the `∀`, same order and binder kinds, `Type*` named `Type u` and `Type v`. |
| 29–32 | `variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]`, `[TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]`, `[IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]`, `[ContinuousSMul G B] [Algebra.IsInvariant A B G]` | The next binders of the `∀`, same order and binder kinds, `Type*` named `Type w`. All eleven instance hypotheses are kept. |
| 36 | `attribute [local instance] Ideal.Quotient.field` | Kept as the same local attribute, at the start of the namespace block. It is not a global instance and does not leave this file. |
| 38 | `include G` | Replaced by binding `{G : Type w}` and its instances inside the `∀` (see below). |
| 40–44 | Theorem docstring | Adapted to describe the proposition. |
| 45–47 | `theorem normal_of_profinite (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P] : Normal (A ⧸ P) (B ⧸ Q)` | The name gets the suffix `Statement`. The explicit ideals, three instance hypotheses and conclusion follow the variable binders unchanged, in this order. |
| 48–99 | Proof | Omitted. It belongs to the later proof unit. |
| 101, 103, 105 | `end Ideal.Quotient`, `end` (section), `end RamificationTheory` | `end Langlands.NYLL.RamificationTheory.Ideal.Quotient`. |

### Universes, implicit parameters and `G`

In the source, the theorem's type quantifies the section variables in
declaration order before its own arguments. So the elaborated source type is
`∀ {A : Type u_1} {B : Type u_2} [CommRing A] … {G : Type u_3} … (P : Ideal A)
(Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P], Normal (A ⧸ P) (B ⧸ Q)`.
The body of `normal_of_profiniteStatement` is this type, with the automatic
universe names `u_1`, `u_2`, `u_3` written as `u`, `v`, `w`. The three universes
remain independent, and `A`, `B`, `G` remain implicit binders.

`G` occurs in no explicit argument and not in the conclusion. In the source,
`include G` therefore makes `G` and every instance mentioning it (lines 29–32)
arguments of the theorem. A theorem would otherwise omit them, and the
hypotheses `Algebra.IsInvariant A B G` and the topological conditions would be
lost. Here the closed `∀` binds `G` and those instances explicitly, at the
same positions, so they have the role `include G` gave them. As in the source,
a user supplies `G` by name. For example, the source consumer at
`ResidueExactSequence.lean` line 410 writes
`normal_of_profinite (G := decompositionGroup K A) P Q`.

### Hypotheses deliberately not changed

- Both `P` and `Q` remain maximal ideals. They are not generalized to
  primes, although the source module docstring speaks of prime residue
  fields. The residue fields are formed with `Ideal.Quotient.field`, which
  needs maximality.
- No Hausdorff (`T2Space`) hypothesis on `G`, no finiteness of `G` and no
  injectivity of `algebraMap A B` is added. No hypothesis of the source is
  dropped.

## Private fidelity checks

The project Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module without
warnings. The inspection of the declaration reports a definition with
universe parameters `u`, `v`, `w` and `statement_returns_prop = true`.

A private draft importing this module, which is not part of this
contribution, also compiled:

1. The source proof, lines 48–99 verbatim, preceded by one `intro` of the
   telescope, proves `normal_of_profiniteStatement.{u, v, w}`.
2. In the source variable context of lines 28–32, with the universes named
   `u`, `v`, `w`, and with `include G`, a proof
   `h` of the statement gives the source conclusion as `h (G := G) P Q`.
3. Conversely, a term of the source theorem's type is accepted as a proof of
   the statement.

These checks support the correspondence with the source and indicate one
proof route. They do not prove the statement. The statement remains a separate
target, and its proof task follows its publication.

## Reuse search

No equivalent is available by Lean name.

- Mathlib's `Ideal.Quotient.normal` (`Mathlib/RingTheory/Invariant/Galois.lean`,
  line 139) has the same conclusion, but it assumes `[Finite G]` and
  `[Algebra.IsInvariant A B G]` without topology. It is the finite case only;
  a profinite `G` may be infinite.
- `Mathlib/RingTheory/Invariant/Profinite.lean` proves integrality
  (`Algebra.IsInvariant.isIntegral_of_profinite`), transitivity on primes and
  surjectivity of the stabilizer homomorphism for profinite groups. It has no
  normality result.
- The supplied Library has no declaration with this conclusion. A task search
  for `normal_of_profinite` and M242 found no duplicate task.

## Dependencies and consumers

The statement uses only Mathlib. It needs no NYLL module, and M242 has no
incoming NYLL dependency in the port inventory. The source consumer is the
instance `decompositionResidueExtension_normal` in
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
(source unit M243). It specializes the theorem to a decomposition group
acting on a discrete valuation subring. This statement supplies no
ramification, residue-action or class-field result.

## Provenance, license and authorship

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
followed by the source path above. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No `notes/errata` directory existed in the workspace, the project or the
supplied Library when this statement was prepared. The source used Lean
4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The
compatibility patch inventory records “none in patch10” for this module. No
compatibility edit was needed.

The original header is kept verbatim: copyright 2026 Naganori Yamaguchi
([upstream author](https://github.com/n-yamaguchi-0729)), all rights reserved;
Apache-2.0; authors Naganori Yamaguchi (assisted by OpenAI Codex). The
existing [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) are unchanged. Their SHA-256
values are `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
equal to the pinned source copies. NOTICE does not list
`ProfiniteInvariant.lean` among its third-party files.

Worker 179 read the source and the Mathlib API, extracted this statement,
ran the checks above and wrote this companion on 10 November 2026. The Lean
header records the modifications.
