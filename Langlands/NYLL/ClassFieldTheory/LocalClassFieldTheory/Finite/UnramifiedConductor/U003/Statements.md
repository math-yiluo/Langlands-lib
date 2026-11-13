# Abelian norm-quotient index target

This module states M372.003 as the Prop-valued definition
`Langlands.NYLL.LocalClassFieldTheory.card_normQuotient_eq_finrank_of_isAbelianGaloisStatement`.
It asserts that the number of elements of the actual norm quotient of a finite
abelian Galois extension of a nonarchimedean local field equals its field degree.
It provides only the target proposition; no proof or finiteness instance is declared.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/UnramifiedConductor.lean`.
The retained source path is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/UnramifiedConductor.lean`.
Its verified SHA-256 is
`0b3ab57df790f21f76557147ff936a8c7d1dc3d7267c160639525a88d130ba0d`.
The source attribution is at lines 1–5, namespace and scope at lines 27–33,
the private finiteness helper M372.001 at lines 35–43, the original docstring
at lines 113–114, and the selected theorem's full signature at lines 115–122.
Its proof is at lines 123–135 and is not extracted here.

The source is available under registered sources
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The published declaration partition, `notes/reuse/nyll-public-port/m361-m384.md`,
identifies this as M372.003 and records no patch10 change to M372.
No applicable NYLL erratum was found in the published Library errata. This
extraction uses the retained original signature directly.

| Source declaration | Published target declaration |
| --- | --- |
| `LocalClassFieldTheory.card_normQuotient_eq_finrank_of_isAbelianGalois` | `Langlands.NYLL.LocalClassFieldTheory.card_normQuotient_eq_finrank_of_isAbelianGaloisStatement` |

The complete target telescope and body are:

```lean
(K L : Type)
[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
[Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] : Prop :=
  Nat.card (Langlands.NYLL.LocalFieldTheory.NormQuotient K L) = Module.finrank K L
```

Both fields remain in universe zero, as in the original `Type` binders; this
definition has no universe parameters. All hypotheses remain explicit binders,
including the base valuation, topology, local-field condition and abelian Galois
condition. There is no valuation or topology on `L` in the selected signature.
`IsNonarchimedeanLocalField` and `IsAbelianGalois` are the actual Mathlib classes.
`Module.finrank K L` is the vector-space dimension of `L` over `K`.

## Actual quotient and reused declarations

The module imports the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U002.Definitions`
and reuses `Langlands.NYLL.LocalFieldTheory.NormQuotient K L` by Lean name.
That declaration is the actual coset quotient
`Kˣ ⧸ Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L`, where the
subgroup is the range of `Langlands.NYLL.LocalFieldTheory.normUnits K L`,
itself `Units.map (Algebra.norm K)`. These declarations and their paired
Markdown were checked before reuse; no quotient or norm is redefined here.

The Mathlib imports are `Mathlib.FieldTheory.Galois.Abelian` for
`IsAbelianGalois`, `Mathlib.NumberTheory.LocalField.Basic` for
`IsNonarchimedeanLocalField`, and `Mathlib.SetTheory.Cardinal.Finite` for
`Nat.card`. `Field`, `ValuativeRel`, `TopologicalSpace`, `Algebra`,
`FiniteDimensional` and `Module.finrank` are also reused from Mathlib through
this import closure. `Nat.card` is defined in the pinned Mathlib file
`Mathlib/SetTheory/Cardinal/Finite.lean`, lines 39–42, as
`Cardinal.toNat (Cardinal.mk α)` with only the type `α` as its argument;
it does not consume a `Finite α` instance. It is zero for an infinite type.
The target itself asks for the cardinal equality, without adding a finiteness
hypothesis or supplying an unproved witness.

## Modification record and compatibility

Worker 330 extracted and documented this unit on 13 November 2026.
The source theorem becomes a `def` returning `Prop`, gains the `Statement`
suffix and the `Langlands.NYLL` namespace prefix, and retains its entire
ordered telescope. The source's `noncomputable section` is retained.
The docstring is adapted to describe the target. Fully qualifying the quotient
removes the need for the source namespace openings and scoped notations.

The result type at source lines 120–122 installs
`letI : Finite (NormQuotient K L) := normQuotientFiniteOfIsAbelianGalois K L`
before the equality. This unused local instance is explicitly erased here.
The private helper at lines 35–43, its proof, and the source theorem's proof
at lines 123–135 are omitted. The erasure requires no construction of a
`Finite` witness: for an arbitrary witness `hFinite`, the following focused
compatibility check compares the two propositions by reflexivity:

```lean
example (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hFinite : Finite (Langlands.NYLL.LocalFieldTheory.NormQuotient K L)) :
    (letI : Finite (Langlands.NYLL.LocalFieldTheory.NormQuotient K L) := hFinite
     Nat.card (Langlands.NYLL.LocalFieldTheory.NormQuotient K L) = Module.finrank K L) =
      Langlands.NYLL.LocalClassFieldTheory.card_normQuotient_eq_finrank_of_isAbelianGaloisStatement K L := rfl
```

The original imports of the conductor and unramified norm-comparison modules,
plus `Mathlib.GroupTheory.Abelianization.Defs`, are omitted. No Artin map,
abelianization equivalence or other conductor result is needed to state this
equality. The partition's preceding-module scheduling dependencies are not
used as mathematical assumptions. No other worker's draft or patch10 code is
reused. The downstream proof will need its own task and accepted proof inputs.

## Validation

Both focused Lean-service checks succeeded with exit code zero, no errors and
no warnings in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The declaration check compiled this entry module and inspected the exact target
name. Inspection reports `kind: definition`, `statement_returns_prop: true`
and `level_parameters: []`, confirming the Prop result and universe-zero
binders. Only the standard assumptions `propext`, `Classical.choice` and
`Quot.sound` occur through the reused Mathlib and quotient declarations.

The private compatibility module imported the public entry module, printed the
full unapplied declaration with universes, assigned that unapplied constant to
the complete ordered telescope above, and checked both the displayed
arbitrary-witness `letI` equality and the plain target body by `rfl`.
Thus the chosen focused import closure compiles and erasing the unused `letI`
is definitionally valid without furnishing any `Finite` instance. These are
checks of the statement and its source correspondence; they do not constitute
independent semantic acceptance or a proof of the target equality.

## Attribution

The original copyright, Apache-2.0 license and author header are retained
verbatim. The unchanged `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are retained with this submission; their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean header and this Markdown explicitly record the adaptation.
