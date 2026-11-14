# NYLL M250.002–M250.004: local scalar instances on the residue subfield of a fixed field

Worker 85, 14 November 2026.

Let `K` be a nonarchimedean local field, `Ω = SeparableClosure K`,
`A = localSeparableValuationSubring K` the chosen valuation ring on `Ω`, `κ_K =
decompositionResidueField K A` the base residue field and `λ =
selectedResidueField A` the residue field of `A`. For a closed subgroup `H` of
`Gal(Ω / K)`, the published definition
`Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedResidueIntermediateField K H`
(M250.001) is an intermediate field `F` of `λ / κ_K`: the subfield generated
over `κ_K` by the image of the residue field over the fixed field of `H`.

This module ports the three `local instance`s that the source declares
right after M250.001: the `κ_K`-algebra structure on `F`, and the scalar action
and module structure underlying it. They add no new mathematics. They name the
standard algebra structure of an intermediate field over its base field. The
source docstring explains why: naming the instances stops typeclass search from
unfolding the fixed-field and residue-action constructions in the later
finite-dimensionality statements.

## Name map

Original names have the prefix `LocalClassFieldTheory.`.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M250.002 | `localAbstractFixedResidueIntermediateFieldAlgebra` | 54–62 | `Langlands.NYLL.PortInternal.M250.d002` | local instance, data (`Algebra`) |
| M250.003 | `localAbstractFixedResidueIntermediateFieldSMul` | 64–70 | `Langlands.NYLL.PortInternal.M250.d003` | local instance, data (`SMul`) |
| M250.004 | `localAbstractFixedResidueIntermediateFieldModule` | 72–78 | `Langlands.NYLL.PortInternal.M250.d004` | local instance, data (`Module`) |

The adapted names are the reserved `PortInternal` names of rows M250.002–M250.004
of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md).
No declaration with any of these names exists in the current Library or
Mathlib.

## The declarations

All three take the source section variables `(K : Type) [Field K]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` and the
explicit closed subgroup `(H : ClosedSubgroup (Gal(SeparableClosure K/K)))`.
`K` lives in `Type`, so none of them has a universe parameter.

```lean
noncomputable local instance _root_.Langlands.NYLL.PortInternal.M250.d002
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))) :
    Algebra
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  (localAbstractFixedResidueIntermediateField K H).algebra

noncomputable local instance _root_.Langlands.NYLL.PortInternal.M250.d003
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))) :
    SMul
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toSMul _ _ _ _
    (Langlands.NYLL.PortInternal.M250.d002 K H)

noncomputable local instance _root_.Langlands.NYLL.PortInternal.M250.d004
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))) :
    Module
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toModule _ _ _ _
    (Langlands.NYLL.PortInternal.M250.d002 K H)
```

- **`d002`** (M250.002) is the `κ_K`-algebra structure on `F`. Its body
  `(localAbstractFixedResidueIntermediateField K H).algebra` uses dot notation
  through the parent structure: `IntermediateField` extends `Subalgebra`, and
  Mathlib has no `IntermediateField.algebra`, so `.algebra` is Mathlib's
  `Subalgebra.algebra` applied to `F.toSubalgebra`. A development probe
  checked that `d002 K H` equals
  `(localAbstractFixedResidueIntermediateField K H).toSubalgebra.algebra` by
  `rfl`. Its structure map sends `a ∈ κ_K` to the image of `a` in `λ` under
  `selectedResidueField.instAlgebra`, which lies in `F`.
- **`d003`** (M250.003) is the scalar action `a • x` of `κ_K` on `F` underlying
  `d002`, namely Mathlib's `Algebra.toSMul` applied to `d002 K H`.
- **`d004`** (M250.004) is the `κ_K`-module structure on `F` underlying `d002`,
  namely Mathlib's `Algebra.toModule` applied to `d002 K H`.

The published objects they use are:

- `localAbstractFixedResidueIntermediateField` (M250.001), module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U001.Definitions`;
- `localSeparableValuationSubring` (M249.006), module
  `...LocalReciprocity.LocalResidueDatum.U006.Definitions`;
- `decompositionResidueField` (M243.003), in
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`,
  with its field instance `decompositionResidueField.instField` (M243.020) and
  the algebra instance `selectedResidueField.instAlgebra` (M243.021) from the
  sibling module `...ResidueExactSequence.ResidueFields`. These instances make
  `F` an intermediate field of `λ / κ_K`.

All three are reached through the single import of M250.001's module.

## Instance scope

In the source, the three are `local instance`s declared inside the
`noncomputable section` that starts at source line 27 and ends at line 459, so
their instance attribute holds only for the rest of that section in
`FiniteSubgroupResidueDegree.lean` and is not exported to importing files. The
adaptation keeps this exactly. All three are `local instance`s declared with
`_root_.` inside the `noncomputable section` of the paired Lean file, which is
nested in the namespace `Langlands.NYLL.LocalClassFieldTheory` like the source
section. After an import they are ordinary named definitions, not instances,
so they cannot conflict with Mathlib or Library instances.

A consumer that needs the source scope installs them in its own section with

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M250.d002
  Langlands.NYLL.PortInternal.M250.d003 Langlands.NYLL.PortInternal.M250.d004
```

A private check (not part of this candidate) that imports the module found:

- `Lean.Meta.isInstance` reports `false` for all three names.
- Without the `attribute [local instance]` line, `#synth` finds
  `Module κ_K F` as Mathlib's `IntermediateField.module'` for `F`.
- With that line, `#synth` returns `Langlands.NYLL.PortInternal.M250.d004 K H`
  for `Module κ_K F` and `Langlands.NYLL.PortInternal.M250.d002 K H` for
  `Algebra κ_K F`, and the source proposition
  `FiniteDimensional κ_K F` of M250.011 elaborates.

## Source and declaration map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean),
SHA-256 `84865498b7b4788c2ebeecb92aeaca7a1bb9a62e2005cb1554386e2a52bf674a`.
The relevant lines are:

- the namespace, opens and section variables, lines 20–34:
  `namespace LocalClassFieldTheory`, `open CyclicCohomology RamificationTheory
  ClassFormation`, `open LocalFieldTheory`, `noncomputable section` (line
  27), `open scoped Pointwise ValuativeRel`,
  `open HilbertRamification.ValuationSubring`,
  `open Field.absoluteGaloisGroup`, and the `variable` line for `K` (33–34);
- M250.002: docstring at lines 54–56, declaration and body at lines 57–62;
- M250.003: declaration and body at lines 64–70 (no docstring);
- M250.004: declaration and body at lines 72–78 (no docstring);
- the end of the section, line 459.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

## Modifications

Worker 85 made only these changes:

1. The namespace `LocalClassFieldTheory` becomes
   `Langlands.NYLL.LocalClassFieldTheory`.
2. The three source names become the reserved names
   `Langlands.NYLL.PortInternal.M250.d002`, `...d003` and `...d004`, written
   with `_root_.`. The bodies of `d003` and `d004` refer to the algebra
   instance by its new name `Langlands.NYLL.PortInternal.M250.d002` instead of
   `localAbstractFixedResidueIntermediateFieldAlgebra`.
3. `d003` and `d004` get docstrings naming their source names; the source has
   none for them. The `d002` docstring is the source docstring, unchanged.
4. The source imports (`...LocalReciprocity.LocalResidueDatum` and
   `...LocalReciprocity.FiniteAbstractFixedField`) are replaced by the single
   published import
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U001.Definitions`.
   Every transitive import lies in the approved Mathlib environment or the
   published Library.
5. Of the source's opens, only `open RamificationTheory` and
   `open HilbertRamification.ValuationSubring` are kept. Inside the new
   namespace they resolve to `Langlands.NYLL.RamificationTheory` and
   `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
   which supply `decompositionResidueField`. `CyclicCohomology`,
   `ClassFormation`, `LocalFieldTheory`, `Field.absoluteGaloisGroup` and the
   scoped `Pointwise` and `ValuativeRel` notations provide nothing these
   declarations use and are omitted.
6. The module gets a module docstring and a modification notice.
7. All other source declarations are omitted (see below).

The `noncomputable section`, the `variable` line, the binders, the types, the
`noncomputable local instance` keywords and the bodies are otherwise unchanged
(source lines 27–34 and 54–78, compared line by line with lines 46–81 of the
adapted file).

A focused `lean_check` of this module in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) reported zero errors and zero
warnings. Inspection of `Langlands.NYLL.PortInternal.M250.d004` reports a
definition with no level parameters and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not
independent acceptance.

## Use downstream and omitted source declarations

Within its own file the source uses these instances only through typeclass
search in the rest of the section. In particular the statements
`FiniteDimensional κ_K F` of
`localAbstractFixedResidueIntermediateField_finiteDimensional` (M250.011,
lines 258–267) and `Module.finrank κ_K F` of
`localResidueDatum_residueDegree_eq_selectedResidueFinrank` (M250.013, lines
336–341) are elaborated with them. The definition M250.012 and the statement
M250.014 install the same structures themselves with `letI`. Outside the file,
the proof of `localResidueDatum_residueDegree_eq_residueFinrank` (M252.004) in
`FiniteResidueFinrankTransfer.lean` refers to `d002` by its source name at
line 251. Adapted consumers install the instances with the
`attribute [local instance]` line above.

The rest of `FiniteSubgroupResidueDegree.lean` is ported in other modules
of the same directory: M250.001 in `U001/Definitions` and the target of
M250.005 in `U005/Statements`. M250.006–M250.014 are separate units.

## Scope

These are three names for the standard algebra, scalar and module structures
of an intermediate field over its base field. No residue-degree, Galois or
reciprocity statement is made here.

## Licence

The original copyright and author header is retained verbatim at the top of
the Lean file: copyright 2026 Naganori Yamaguchi, all rights reserved; authors
Naganori Yamaguchi (assisted by OpenAI Codex); Apache-2.0. A modification
notice follows it. The retained files are
[`licenses/NYLL/LICENSE`](../../../../../../../../licenses/NYLL/LICENSE),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and [`licenses/NYLL/NOTICE`](../../../../../../../../licenses/NYLL/NOTICE),
SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 85 adapted these units directly from the pinned original; no other
project worker supplied code.
