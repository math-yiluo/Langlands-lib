# NYLL M152.003, M152.024, M152.027: targets for the normal-basis lattice basis and the Galois action on its coordinates

The paired Lean file adapts the statements of three theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`.
The pinned source file has SHA-256
`affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `LocalClassFieldTheory.` | `omit` | Docstring | Attribute | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.LocalClassFieldTheory.` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| M152.003 | `chosenNormalBasisIntegerLatticeBasis_apply` | — | 53 | 54 | 55–57 | 57–58 | `chosenNormalBasisIntegerLatticeBasis_applyStatement` |
| M152.024 | `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe` | 430 | 431 | 432 | 433–436 | 436–437 | `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coeStatement` |
| M152.027 | `chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup` | 459 | 460–461 | — | 462–466 | 466–493 | `chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement` |

M152.003 lies before the section `GradedCoordinates`, the other two inside
it, each with the source line
`omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in`.

The source file `NormalBasis.lean` imports
`Nyll.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice`,
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic`,
`Mathlib.FieldTheory.Galois.NormalBasis` and
`Mathlib.LinearAlgebra.Quotient.Pi` (lines 7–10). Its context is
`namespace LocalClassFieldTheory` (line 16), `open LocalFieldTheory`
(line 18), `open CyclicCohomology` (line 20), `noncomputable section`
(line 22), `universe u` (line 24), `open scoped ValuativeRel` (line 26),
the section variables of lines 28–29,

```lean
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
```

the section `GradedCoordinates` (lines 60 and 749) with its variables
`[TopologicalSpace K] [IsNonarchimedeanLocalField K]` (line 62), and the
closing lines 751–752. This context is kept verbatim, in the same order.

The elaborated telescopes, printed with `#check` in the project Lean
service, begin with `(K L : Type u) [Field K] [ValuativeRel K] [Field L]
[Algebra K L] [FiniteDimensional K L] [IsGalois K L]`. Only
`chosenNormalBasisIntegerLatticeMulPowLinearMap` also has
`[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, which the chosen
uniformizer `π_K` needs. The Galois-action equivalence does not use these
two instances, and Lean does not include them; the two theorems after it
omit them explicitly. The telescope of M152.003 is exactly the one of lines 28–29. Each
target is a `Prop`.

The statements use the Galois-action equivalence M152.023
`galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`, ported in the
companion module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions` of this contribution, the
published lattice basis `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis` (M152.002,
in `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.IntegerLatticeBasis`), the basis of the lattice indexed by
`Gal(L/K)` whose vectors are those of Mathlib's normal basis, and the
published normal-basis lattice
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisIntegerLattice K L`
(M144.002, in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions`, found through the source line
`open CyclicCohomology`). Mathlib supplies `IsGalois.normalBasis`,
`Module.Basis.equivFun`, `Gal(L/K)` with its group structure and its
action on `L`.

## Targets and complete telescopes

### M152.003

```lean
/-- Target: the integral lattice basis has the same underlying vectors as the
chosen normal basis. -/
def chosenNormalBasisIntegerLatticeBasis_applyStatement (σ : Gal(L/K)) : Prop :=
    ((chosenNormalBasisIntegerLatticeBasis K L σ :
      chosenNormalBasisIntegerLattice K L) : L) = IsGalois.normalBasis K L σ
```

For `σ ∈ Gal(L/K)`, the `σ`-th vector of the lattice basis, viewed in `L`,
is the `σ`-th vector of Mathlib's normal basis.

### M152.024

```lean
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Target: the restricted lattice equivalence agrees with the ambient Galois
action. -/
def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coeStatement
    (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) : Prop :=
    ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x :
      chosenNormalBasisIntegerLattice K L) : L) = τ (x : L)
```

For `τ ∈ Gal(L/K)` and `x` in the lattice, the image of `x` under the
equivalence M152.023, viewed in `L`, is `τ x`.

### M152.027

```lean
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Target: normal-basis lattice coordinates obey the left-regular rule before
the inverse-index reindexing. -/
def chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement
    (τ σ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) : Prop :=
    (chosenNormalBasisIntegerLatticeBasis K L).equivFun
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) σ =
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun x (τ⁻¹ * σ)
```

For `τ, σ ∈ Gal(L/K)` and `x` in the lattice, the `σ`-coordinate of `τ x`
in the lattice basis is the `τ⁻¹ σ`-coordinate of `x`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.LocalClassFieldTheory`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line, and the line
   breaks are otherwise those of the source. The source proofs are omitted:
   this contribution publishes the proposition targets, and their proofs
   are separate work.
3. Omit the `@[simp]` attributes of M152.003 and M152.024: a definition of
   a proposition is not a simp lemma. Keep the `omit` lines of M152.024 and
   M152.027.
4. Prefix each source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
5. Replace the four source imports by the companion module
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions`, which imports the published modules of
   the names listed above.
6. Keep the source context listed above; omit the two definitions (ported
   in the companion module) and the other declarations of the source file.
7. No helper declaration, instance or linter option is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
