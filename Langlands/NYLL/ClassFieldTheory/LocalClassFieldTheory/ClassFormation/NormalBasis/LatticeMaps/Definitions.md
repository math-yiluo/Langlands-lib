# NYLL M152.004, M152.023: uniformizer scaling and the Galois action on the normal-basis lattice

The paired Lean file adapts two definitions of Naganori
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

| Unit | Source definition after `LocalClassFieldTheory.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.LocalClassFieldTheory.` |
| --- | --- | --- | --- | --- | --- |
| M152.004 | `chosenNormalBasisIntegerLatticeMulPowLinearMap` | 64–65 | 66–68 | 69–81 | `chosenNormalBasisIntegerLatticeMulPowLinearMap` |
| M152.023 | `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv` | 400 | 401–403 | 404–428 | `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv` |

The source section comment `/-! ### The actual Gal(L / K) action and
right-regular equivariance -/` (line 398) is kept before M152.023.

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
omit them explicitly.

The published NYLL declarations used are, in `Langlands.NYLL.CyclicCohomology`
(opened by the source line `open CyclicCohomology`, which inside
`Langlands.NYLL.LocalClassFieldTheory` resolves to `Langlands.NYLL.CyclicCohomology`), the
normal-basis lattice `chosenNormalBasisIntegerLattice K L` (M144.002, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions`), the dilated submodule
`chosenBaseUniformizerPowSubmodule K L n N` (M144.014, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions`), the membership criterion
`mem_chosenBaseUniformizerPowSubmodule_iff` (M144.015, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U015.Proofs`; its type is the published target
`mem_chosenBaseUniformizerPowSubmodule_iffStatement K L n N x`, the
equivalence of `x ∈ chosenBaseUniformizerPowSubmodule K L n N` with
`∃ y : L, y ∈ N ∧ algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x`)
and the stability theorem
`galoisGroup_apply_mem_chosenNormalBasisIntegerLattice` (M144.007, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U007.Proofs`; its type is the published target
`galoisGroup_apply_mem_chosenNormalBasisIntegerLatticeStatement K L τ hx`,
the proposition `τ x ∈ chosenNormalBasisIntegerLattice K L`); and, in
`Langlands.NYLL.LocalFieldTheory`, the chosen uniformizer
`chosenIntegerRingUniformizer K` (M133.004, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Definitions`).
The source uses the two theorems through `.2` and as a proof term, and both
uses are accepted unchanged because the Statement types unfold to the source
propositions. Mathlib supplies `LinearMap`, `LinearEquiv`, `Gal(L/K)` with
`AlgEquiv.commutes`, `symm_apply_apply`, `apply_symm_apply` and `map_add`,
`algebraMap`, `Subtype.ext`, `Submodule.coe_smul`, `Algebra.smul_def`,
`map_mul`, `mul_add`, `mul_assoc`, `mul_comm` and `mul_left_comm`.

The other declarations of the source file are not part of this module;
M152.001 `span_normalBasis_eq_chosenNormalBasisIntegerLattice` and M152.002
`chosenNormalBasisIntegerLatticeBasis` are already published, and the
statements of the theorems M152.003, M152.024 and M152.027 are in the
companion module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Statements` of this contribution.

## Definitions

### M152.004

```lean
/-- Multiplication by `π_K^n`, from the normal-basis lattice onto its
`n`-th dilate. -/
def chosenNormalBasisIntegerLatticeMulPowLinearMap (n : Nat) :
    chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) where
  toFun x :=
    ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L),
      (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) _).2
        ⟨x, x.2, rfl⟩⟩
  map_add' := by
    intro x y
    ext
    exact mul_add _ _ _
  map_smul' := by
    intro a x
    ext
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]
```

For a natural number `n`, the definition is the `𝒪_K`-linear map from the
normal-basis lattice `M` to its dilate `π_K^n M` sending `x` to
`π_K^n x`. Membership in the dilate is given by M144.015 with witness `x`;
the two tactic blocks prove additivity and `𝒪_K`-linearity.

### M152.023

```lean
/-- The actual Galois action restricted to the stable normal-basis lattice. -/
def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv (τ : Gal(L/K)) :
    chosenNormalBasisIntegerLattice K L ≃ₗ[𝒪[K]]
      chosenNormalBasisIntegerLattice K L where
  toFun x := ⟨τ (x : L),
    galoisGroup_apply_mem_chosenNormalBasisIntegerLattice (K := K) (L := L) τ x.2⟩
  invFun x := ⟨τ⁻¹ (x : L),
    galoisGroup_apply_mem_chosenNormalBasisIntegerLattice (K := K) (L := L) τ⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact τ.symm_apply_apply (x : L)
  right_inv x := by
    apply Subtype.ext
    exact τ.apply_symm_apply (x : L)
  map_add' x y := by
    apply Subtype.ext
    exact map_add τ (x : L) (y : L)
  map_smul' a x := by
    apply Subtype.ext
    have ha : τ (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change τ (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact τ.commutes (a : K)
    change τ (((a • x : chosenNormalBasisIntegerLattice K L) : L)) =
      ((a • (⟨τ (x : L), galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) τ x.2⟩ : chosenNormalBasisIntegerLattice K L) :
          chosenNormalBasisIntegerLattice K L) : L)
    rw [Submodule.coe_smul, Submodule.coe_smul]
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [map_mul, ha]
```

For `τ ∈ Gal(L/K)`, the definition is the `𝒪_K`-linear automorphism of the
lattice `M` given by `x ↦ τ x`, with inverse `x ↦ τ⁻¹ x`. Stability of `M`
is M144.007; the tactic blocks prove the two inverse laws, additivity and
`𝒪_K`-linearity (using that `τ` fixes the image of `𝒪_K`).

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definitions are
   `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap` and
   `Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`.
2. Copy the docstrings, the binders, the bodies and the section comment
   verbatim, with the source line breaks; a line diff against the pinned
   source shows no difference in either declaration.
3. Replace the four source imports by the three published modules
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.IntegerLatticeBasis` (M152.002), `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U007.Proofs` and
   `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U015.Proofs`, which import the modules of all names listed
   above, and the source module docstring by a description of this module
   with a modification notice.
4. Keep the source context listed above; omit the other declarations of
   the source file.
5. No helper declaration, instance or linter option is added.

These are definitions only. They discharge no host class-formation, Tate or
reciprocity target.

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
