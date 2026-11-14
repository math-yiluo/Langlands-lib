# The embedded intrinsic-to-ambient base equivalence as a homeomorphism

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean`
(file SHA-256 `d8403d819db83b085b6fad6144c82340f414f44f5675e495b83e79ffd28ee1a1`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The source
file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M281.004 | def `intrinsicBaseContinuousEquivAmbientEmbeddedField` (docstring 287–288, signature 289–301, body 302–317) | `intrinsicBaseContinuousEquivAmbientEmbeddedField` |

The original name is in the source namespace `LocalClassFieldTheory`; the
adapted name is
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseContinuousEquivAmbientEmbeddedField`.

## Parameters and type

```lean
noncomputable def
    intrinsicBaseContinuousEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃ₜ*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup
```

All fields are in `Type` (universe zero), as in the source. The parameters
and the two `letI` algebra structures are exactly those of the published
`intrinsicBaseEquivAmbientEmbeddedField` (M273.006): `SeparableClosure F` is
an `F`-algebra through its definition as the separable closure of `F` in
`AlgebraicClosure F`, and `SeparableClosure K` is made an `F`-algebra by the
embedding `i`.

## Content

Write `Ω := SeparableClosure K`. The domain `(intrinsicAbstractBase F).toSubgroup`
is the closed fixing subgroup of `⊥` in `intrinsicAbsoluteGalois F =
Gal(SeparableClosure F / F)`, and the codomain is the closed fixing subgroup of
the field range of `i` in `Gal(Ω / K)`. Both carry the subspace topologies
induced by the Krull topologies.

For `e : SeparableClosure F ≃ₐ[F] Ω`, the definition is the continuous
multiplicative equivalence between these subgroups whose underlying
multiplicative equivalence is `intrinsicBaseEquivAmbientEmbeddedField K F i e`.
The body, copied from the source, works as follows.

1. It installs the `F`-algebra structure on `Ω` given by `i` and introduces `e`.
2. `psi := intrinsicBaseEquivAmbientEmbeddedField K F i e`, and
   `hpsi : Continuous psi` is the published theorem
   `intrinsicBaseEquivAmbientEmbeddedField_continuous K F i e` (M281.003).
3. It registers the local instance `CompactSpace (intrinsicAbstractBase F).toSubgroup`.
   The proof applies `isCompact_iff_compactSpace.mp` to `IsClosed.isCompact`
   of the closedness field `isClosed'` of the closed subgroup
   `intrinsicAbstractBase F`. The ambient group `Gal(SeparableClosure F / F)`
   is compact by a Mathlib instance for Galois groups of Galois extensions.
4. The result is `{ toMulEquiv := psi, continuous_toFun := hpsi, continuous_invFun := ... }`.
   The inverse is continuous by Mathlib's
   `Continuous.continuous_symm_of_equiv_compact_to_t2`: a continuous bijection
   from a compact space to a Hausdorff space has continuous inverse. The
   codomain is Hausdorff as a subspace of the Hausdorff Krull topology on
   `Gal(Ω / K)`; Lean finds this by Mathlib instances.

The data is only `toMulEquiv`; the two continuity fields are proofs. In
particular, the coercion of `intrinsicBaseContinuousEquivAmbientEmbeddedField K F i e`
to a function is definitionally the coercion of
`intrinsicBaseEquivAmbientEmbeddedField K F i e`. A private check confirmed
this by `rfl` and confirmed the compactness and Hausdorff instances by
`#synth`. The check is not part of this candidate.

Published components used, all by their Library names:

- `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField`
  (M273.006), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`;
- `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous`
  (M281.003), from the imported module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U003.Proofs`.
  Its type is the published closed proposition
  `intrinsicBaseEquivAmbientEmbeddedField_continuousStatement` of
  `EmbeddedFrobeniusTransport/U002/Statements`;
- `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (M091.003) and
  `intrinsicAbsoluteGalois` (M091.001), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`;
- `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`, from
  `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`.

The single import, `EmbeddedFrobeniusTransport.U003.Proofs`, makes all of
these available.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The definition is placed in its own file
  `EmbeddedFrobeniusTransport/U004/Definitions`.
- The source imports `Mathlib.FieldTheory.Galois.Basic`, five
  `FixedFieldIntrinsicReciprocity.BaseComparison` modules and
  `ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv` (lines
  7–13). The port imports only the published module
  `EmbeddedFrobeniusTransport.U003.Proofs` described above.
- The source opens `LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory`,
  `ClassFormation` and `scoped ValuativeRel` (lines 28–30). The port opens only
  `RamificationTheory`, for `closedFixingSubgroup`; the others are not used by
  this definition.
- The docstring, the keywords `noncomputable def`, the binders, the result
  type and the tactic body are copied from source lines 287–317 without
  change, inside the source's `noncomputable section` (line 24).
- No other declaration of the source module is included. The next source
  definition, `intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField`
  (M281.005, lines 319 onward), uses this one and is not part of this unit.

## Library and Mathlib comparison

A search of the Library `.lean` files at commit
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86` found no declaration named
`intrinsicBaseContinuousEquivAmbientEmbeddedField` and no other continuous
multiplicative equivalence (`≃ₜ*`) out of `intrinsicAbstractBase F` or into a
`closedFixingSubgroup`. The search covered every Library file containing
`≃ₜ*` together with `SeparableClosure`, `closedFixingSubgroup`,
`fixingSubgroup` or `Gal(`. The closest declarations are:

- `Langlands.Weil.Local.extensionGaloisEquivRange` (`Langlands/Weil/Local/ExtensionGalois.lean`),
  which, for an embedding `f` of `p`-adic fields (`PadicField p`), identifies
  `Field.absoluteGaloisGroup E` with the range of the restriction map
  `extensionGaloisMap F E f`;
- `Langlands.ClassFieldTheory.Local.AbsoluteRestriction.groupEquiv`
  (`Langlands/ClassFieldTheory/Local/AbsoluteRestrictionImage.lean`), which,
  under `[CharZero K]`, identifies `Field.absoluteGaloisGroup L` with an open
  subgroup of `Field.absoluteGaloisGroup K`;
- `Langlands.ClassFieldTheory.Local.closureSubgroupEquiv`
  (`Langlands/ClassFieldTheory/Local/ClosureRestrictionTransport.lean`), which,
  under `[CharZero K]` and for a normal intermediate field `E` of
  `AlgebraicClosure K / K`, identifies `Field.absoluteGaloisGroup E` with
  `E.fixingSubgroup`.

These use absolute Galois groups built from algebraic closures, not the NYLL
intrinsic base `intrinsicAbstractBase F` in `Gal(SeparableClosure F / F)`, and
none of them is built from `intrinsicBaseEquivAmbientEmbeddedField`. Their
inverse-continuity proofs use the compact/Hausdorff principle.
`AbsoluteRestriction.groupEquiv` and `closureSubgroupEquiv` use
`Continuous.continuous_symm_of_equiv_compact_to_t2` directly;
`extensionGaloisEquivRange` instead uses `isEmbedding.continuous_iff`
for its established closed embedding.
None of them has the type of this definition, which holds for arbitrary fields `K` and `F`. Mathlib has the general
constructor used in the body, but no declaration specialised to these Galois
subgroups.

The original copyright and author header is retained in the Lean file,
followed by a dated modification record. Apache-2.0 attribution and notices
are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
