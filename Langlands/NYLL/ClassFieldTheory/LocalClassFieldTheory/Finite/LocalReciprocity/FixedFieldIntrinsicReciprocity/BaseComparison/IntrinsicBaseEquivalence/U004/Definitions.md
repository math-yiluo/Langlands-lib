# Intrinsic-to-ambient base equivalences

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`
(file SHA-256 `0c4403626ce06952a02d1bd927112542e4f69466ca939a1d0896195d94ef5800`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M273.004 | `intrinsicBaseEquivAmbientFixedField` (148–171) | `intrinsicBaseEquivAmbientFixedField` |
| M273.006 | `intrinsicBaseEquivAmbientEmbeddedField` (193–307) | `intrinsicBaseEquivAmbientEmbeddedField` |

The original names are in `LocalClassFieldTheory`; the adapted names are
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField` and
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField`.
The source context used is the header (lines 1–5), `noncomputable section`
(line 20), the namespace (line 22) and the `open` lines (24–26).

## Content

Both definitions are multiplicative equivalences. They identify the intrinsic
base subgroup of a field with a closed subgroup of the absolute Galois group
`Gal(SeparableClosure K / K)` of a smaller field `K`.

**`intrinsicBaseEquivAmbientFixedField K H e`** (M273.004). The inputs are a
field `K : Type` and a finite abstract field `H` over
`Gal(SeparableClosure K / K)`. Such an `H` is a closed subgroup `H.field` with
finitely many cosets in the distinguished base subgroup. Let
`F := abstractFixedField K (SeparableClosure K) H.field` be the fixed field of
`H.field`. The last input is an `F`-algebra equivalence
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K`. The result is an
equivalence

`(intrinsicAbstractBase F).toSubgroup ≃* H.field.toSubgroup`.

It is the composite of three maps:

1. `intrinsicAbstractBaseEquivAbsolute F`, from the intrinsic base subgroup to
   `Gal(SeparableClosure F / F)`;
2. conjugation by `e`, which is `AlgEquiv.autCongr e`, to
   `Gal(SeparableClosure K / F)`;
3. the inverse of `abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H.field`,
   from that group back to the subgroup `H.field`.

The `F`-algebra structure on `SeparableClosure F` is written in the type as
`(separableClosure F (AlgebraicClosure F)).algebra`, as in the source.

**`intrinsicBaseEquivAmbientEmbeddedField K F i e`** (M273.006). The inputs
are fields `K F : Type` with `F` a finite-dimensional separable `K`-algebra, a
`K`-algebra embedding `i : F →ₐ[K] SeparableClosure K`, and an `F`-algebra
equivalence `e : SeparableClosure F ≃ₐ[F] SeparableClosure K`. Here
`SeparableClosure K` is an `F`-algebra through `i`. The result is an
equivalence

`(intrinsicAbstractBase F).toSubgroup ≃* (closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)).toSubgroup`.

The construction, as in the source, is the following.

- `H₀` is the closed subgroup fixing the image `i.fieldRange`. It is bundled
  as a finite abstract field `H`. Its finiteness proof is the published
  theorem `ambientEmbeddedAbsoluteQuotientFinite K F i` (M273.001).
- `F₀` is the fixed field of `H₀`. Mathlib's
  `InfiniteGalois.fixedField_fixingSubgroup` gives `F₀ = i.fieldRange`. So
  `F` and `F₀` are isomorphic over `K`, by `i.equivFieldRange` followed by
  `IntermediateField.equivOfEq`.
- `e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K` is Mathlib's
  `IsSepClosure.equiv`.
- The ring equivalence `c := e` followed by `e₀⁻¹` maps
  `SeparableClosure F` to `SeparableClosure F₀`. It is compatible with the
  isomorphism `F ≃ F₀`. Conjugation by `c` gives
  `theta : Gal(SeparableClosure F / F) ≃* Gal(SeparableClosure F₀ / F₀)`,
  written out explicitly as in the source.
- The result is the composite of four maps: `intrinsicAbstractBaseEquivAbsolute F`,
  then `theta`, then the inverse of `intrinsicAbstractBaseEquivAbsolute F₀`,
  then `intrinsicBaseEquivAmbientFixedField K H e₀`.

The published declarations used are listed below. All are used by their
Library names.

| Name | Unit |
| --- | --- |
| `FiniteAbstractField` | M010.121 |
| `baseField` | M010.003 |
| `le_baseField` | M010.005 |
| `extensionSubgroup` | M004.002 |
| `closedFixingSubgroup` | M087.001 |
| `intrinsicAbsoluteGalois` | M091.001 |
| `intrinsicAbstractBase` | M091.003 |
| `intrinsicAbstractBaseEquivAbsolute` | M091.004 |
| `abstractFixedField` | M099.001 |
| `abstractSubgroupEquivGaloisGroup` | M099.007 |
| `ambientEmbeddedAbsoluteQuotientFinite` | M273.001 |

`ambientEmbeddedAbsoluteQuotientFinite` is the proof of M273.001 in module
`...IntrinsicBaseEquivalence.U001.Proofs`. All other names in the table are
definitions or proved theorems.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The two definitions are placed together in a separate `U004/Definitions`
  module.
- **Imports.** The source imports `Mathlib.FieldTheory.Galois.Basic`,
  `...LocalReciprocity.FixedFieldLocalData` and
  `...LocalReciprocity.IntrinsicAbsoluteData`. The port imports instead the
  four published modules that supply the names in the table:
  - `...Degree.Fields.FiniteAbstractField.Definitions`;
  - `...FiniteAbstractFixedField.Initial.Definitions`;
  - `...IntrinsicAbsoluteData.U004.Definitions`;
  - `...IntrinsicBaseEquivalence.U001.Proofs`.
- **Openings.** The source opens
  `LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory`,
  `ClassFormation` and `scoped ValuativeRel`. The port opens only
  `RamificationTheory CyclicCohomology` and `ClassFormation`. Inside
  `Langlands.NYLL` these resolve to the `Langlands.NYLL` namespaces. The other
  openings are not used by these two definitions.
- The docstrings, `noncomputable` modifiers, binders (all fields in `Type`),
  result types and tactic bodies are copied verbatim from the source, with one
  exception, described next.
- **Finite-dimensionality instance in M273.006.** The source body contains the
  local instance

  `letI : FiniteDimensional K F₀ := abstractFixedField_finiteDimensional K (SeparableClosure K) H₀ hHabsolute`.

  The theorem `abstractFixedField_finiteDimensional` is source unit M099.005.
  At Library commit `451cce4ca176c34856be86a36801b7a3b585ae77` it is published
  only as the proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensionalStatement`,
  without a proof. The port therefore proves the same instance another way.
  The proof transports finite-dimensionality from `F` along the `K`-algebra
  equivalence `(AlgEquiv.ofInjectiveField i).trans (IntermediateField.equivOfEq h)`,
  where `h` is `(InfiniteGalois.fixedField_fixingSubgroup (AlgHom.fieldRange i)).symm`
  (Mathlib). The instance is a proposition, so the definition does not depend
  on which proof is used.

A private check, not part of the candidate, confirms three things:

- The verbatim source body of M273.006 is equal by `rfl` to the adapted
  definition. In this check the source body takes the M099.005 proposition as
  a hypothesis. The unused-variable linter also reports that hypothesis as
  unreferenced, so the instance does not enter the elaborated term.
- The source proof of the simp lemma
  `intrinsicBaseEquivAmbientFixedField_apply_val` (M273.005, lines 173–191),
  `dsimp only; rintro e τ; rfl`, goes through for the adapted M273.004.
- The `U004/Definitions` module itself compiles with no errors and no warnings.

M273.005 is a theorem and is not part of this candidate. The other source
declarations in the file are M273.001–.003 and M273.007–.009. They are
theorems and are also omitted.

## Library and Mathlib comparison

No Library declaration has either type. In Library `.lean` files,
`intrinsicAbstractBase` occurs only in its defining module, in the M091.004
module and in the abbreviation `Langlands.NYLL.PortInternal.M097.d003`, which
restates it. None of them is an equivalence with an ambient fixing subgroup.

`Langlands.ClassFieldTheory.Local.closureSubgroupMulEquiv` (in
`Langlands/ClassFieldTheory/Local/ClosureRestrictionTransport.lean`) is a
related but different equivalence. It identifies
`Field.absoluteGaloisGroup E` with `E.fixingSubgroup` for an intermediate field
`E` of `AlgebraicClosure K`, by restriction along a fixed closure equivalence.
It uses algebraic closures rather than separable closures. It takes no
equivalence `e` as input. Its domain is the absolute Galois group itself
rather than the intrinsic base subgroup.

Mathlib's `IntermediateField.fixingSubgroupEquiv` and
`AlgEquiv.autCongr` are building blocks of these definitions (through
`abstractSubgroupEquivGaloisGroup` and directly). Mathlib does not provide the
composites.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
