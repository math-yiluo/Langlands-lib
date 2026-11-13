# Finite Frobenius action on finite Galois intermediate fields

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M168.001 | `finiteResidueFrobeniusIntermediate` (39–45) | `finiteResidueFrobeniusIntermediate` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

For a field `k : Type u` with `[Fintype k]` and a `k`-algebra field
`Omega : Type v`, and a finite Galois intermediate field
`E : FiniteGaloisIntermediateField k Omega`,
`finiteResidueFrobeniusIntermediate k Omega E : ZHatMul →ₜ* (E ≃ₐ[k] E)` is the
published `finiteResidueFrobeniusFromZHat k E` (the action of `ℤ̂` on `E` through
reduction modulo `[E : k]`), with the instance `Finite E` obtained in the body
from `Module.finite_of_finite k` (finite-dimensionality over the finite base).

## Modifications

- Namespace prefixed by `Langlands.NYLL`; the source `variable` block
  (lines 35–37, including `[IsGalois k Omega]`), universes, `open` commands
  (`ClassFormation`, `CategoryTheory`, `Opposite`,
  `FiniteGaloisIntermediateField`, `ProfiniteGrp`), the type, the tactic body
  and the `noncomputable section` are retained. As in the source, the
  definition uses neither `[IsGalois k Omega]` nor any other unused section
  instance, so Lean does not make it a parameter (the source definition has the
  same parameter list).
- The source import of the NYLL `FiniteResidueFrobenius` module is replaced by
  the published `Langlands.NYLL` port of its definitions
  (`.../FiniteResidueFrobenius/Definitions`).
- The later data commands M168.002 (private `residueFrobeniusLimitPoint`),
  M168.003 `residueFrobeniusToLimit` and M168.005 `residueAbsoluteFrobenius`
  are not part of this module: M168.002's body needs the proof of M167.018, and
  the other two are built from it.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
