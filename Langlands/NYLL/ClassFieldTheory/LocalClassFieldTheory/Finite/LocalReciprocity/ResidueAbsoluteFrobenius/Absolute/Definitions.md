# Absolute Frobenius action of the profinite integers on an algebraic Galois extension

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M168.002 (private) | `residueFrobeniusLimitPoint` (47–63) | inlined as the `toFun` of `residueFrobeniusToLimit` |
| M168.003 | `residueFrobeniusToLimit` (65–97) | `residueFrobeniusToLimit` |
| M168.005 | `residueAbsoluteFrobenius` (108–113) | `residueAbsoluteFrobenius` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.
`ZHat` and `ZHatMul` are the published `Langlands.NYLL.ClassFormation`
declarations.

## Content

Throughout, `k : Type u` is a field with `[Fintype k]` and `Omega : Type v` is
a field with a `k`-algebra structure. The source `variable` block (lines 35–37,
retained verbatim) also declares `[IsGalois k Omega]`, but as explained below
only `residueAbsoluteFrobenius` takes it as a parameter. Mathlib's functor
`InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega`, sending a finite Galois
intermediate field `E` to `Gal(E/k)` on the opposite category of finite Galois
intermediate fields, exists for any field extension `Omega/k`. For a Galois
extension, the continuous multiplicative equivalence
`InfiniteGalois.continuousMulEquivToLimit k Omega` identifies `Gal(Omega/k)`
with the limit of this functor.

- `residueFrobeniusToLimit k Omega :
  ZHatMul →ₜ* limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega)`
  sends `z` to the compatible family whose coordinate at a finite Galois
  intermediate field `E` is the published M168.001
  `finiteResidueFrobeniusIntermediate k Omega E z`, the action of `z` on `E`
  through reduction modulo `[E : k]`. The family is compatible: for `F ≤ E`,
  restriction to `F` of the coordinate at `E` is the coordinate at `F`, which is
  the published M167.018 theorem `restrictNormalHom_finiteResidueFrobeniusFromZHat`
  for the tower `k ⊆ F ⊆ E`. The map is multiplicative coordinatewise, and
  continuous because each coordinate is continuous for the Krull topology, which
  on a finite Galois group is the discrete topology of the limit diagram.
- `residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)` is
  `residueFrobeniusToLimit k Omega` followed by the inverse of
  `InfiniteGalois.continuousMulEquivToLimit k Omega`: the canonical continuous
  homomorphism `ℤ̂ → Gal(Omega/k)` assembled from the finite Frobenius actions.
  No bijectivity is claimed or used.

A definition takes only the section binders it uses, so the two signatures differ:

- `residueFrobeniusToLimit` has parameters `(k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]` and no Galois
  hypothesis. Assembling the finite Frobenius coordinates into a compatible
  family in the limit needs only the functor
  `InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega` and the M168.001 data,
  and neither requires `Omega/k` to be Galois.
- `residueAbsoluteFrobenius` additionally takes `[IsGalois k Omega]`, through
  `InfiniteGalois.continuousMulEquivToLimit k Omega`. That hypothesis is needed
  only to identify the limit with `Gal(Omega/k)`.

These are the parameters of the source definitions. In the source, the
component theorem M168.004 about `residueFrobeniusToLimit` (lines 99–106) states
`omit [IsGalois k Omega]` explicitly.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; the source `variable` block,
  universes, `open` commands (`ClassFormation`, `CategoryTheory`, `Opposite`,
  `FiniteGaloisIntermediateField`, `ProfiniteGrp`), the types, the tactic
  bodies and the `noncomputable section` are retained.
- The private M168.002 `residueFrobeniusLimitPoint` is written in place as the
  `toFun` field of `residueFrobeniusToLimit`, its only use among the adapted
  rows: its `val` and its compatibility proof are the source body unchanged. No
  `PortInternal` declaration is introduced.
- The source import of the NYLL `FiniteResidueFrobenius` module is replaced by
  the published M168.001 module `...ResidueAbsoluteFrobenius.Initial.Definitions`
  and the published proof module of M167.018,
  `...FiniteResidueFrobenius.U018.Proofs`, whose theorem the compatibility proof
  uses by name.
- The source `@[simp]` theorem M168.004 `residueFrobeniusToLimit_apply_component`
  (lines 99–106) is outside Task 5860 and not adapted. The theorems M168.006,
  M168.007 and M168.009 have their targets in the sibling `Absolute/Statements`
  module.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
