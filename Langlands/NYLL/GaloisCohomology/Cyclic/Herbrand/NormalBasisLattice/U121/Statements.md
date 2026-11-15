# NYLL M144.122: target that the next principal-unit level lies in the kernel

The paired Lean file adapts the statement of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`.
The pinned source file has SHA-256
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `CyclicCohomology.` | `omit` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.CyclicCohomology.` |
| --- | --- | --- | --- | --- | --- | --- |
| M144.122 | `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ` | 2159–2160 | 2161 | 2162–2175 | 2175–2187 | `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement` |

The source file `NormalBasisLattice.lean` imports
`Mathlib.FieldTheory.Galois.NormalBasis`,
`Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients`
and
`Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension`
(lines 7–9). Its second part, which contains the ported declarations, opens
with `universe u` (line 1626), `namespace CyclicCohomology` (line 1628),
`open LocalFieldTheory` (line 1630), `noncomputable section` (line 1632),
`open scoped ValuativeRel` and `open Filter` (lines 1634–1635) and the
section variables of lines 1637–1640,

```lean
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
```

and closes with lines 2296–2297. This context is kept verbatim, in the same
order.

The source theorem omits the instance
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`
(lines 2159–2160), and the port keeps that `omit` line. The elaborated
telescope, printed with `#check` in the project Lean service, is
`(K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
[IsGalois K L] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K] [ValuativeRel L]`, followed by the binders
shown below, and the target is a `Prop`.

The statement uses the homomorphism M144.121
`chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom`, ported in the
companion module `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.Definitions` of this contribution. The published NYLL declarations used, all in `Langlands.NYLL.CyclicCohomology`, are the
normal-basis lattice `chosenNormalBasisIntegerLattice K L` (M144.002, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions`), the dilated submodule
`chosenBaseUniformizerPowSubmodule K L n N`, the image of `N` under
multiplication by `π_K^n` (M144.014, in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions`), the
level-`n` principal-unit set `chosenNormalBasisPrincipalUnitSet K L n` of
units `u` of `𝒪_L` with `u - 1` in the `n`-th dilate of the lattice
(M144.059, in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions`), the successive quotient
`chosenNormalBasisLatticeSuccQuot K L n` of the `n`-th dilate by the
`(n + 1)`-st (M144.087, in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U086.Definitions`, with its instance
`chosenNormalBasisLatticeSuccQuotAddCommGroup` of the same module, which
gives `Multiplicative` of it the group structure used by the target
`MonoidHom`) and the class map
`chosenNormalBasisPrincipalUnitLatticeClass K L n u hu`, the class of
`u - 1` in that quotient (M144.102, in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U102.Definitions`).
Mathlib supplies `Subgroup`, the units `𝒪[L]ˣ` and `MonoidHom.ker`.

## Target and complete telescope

```lean
omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
set_option linter.unusedVariables false in
/-- Target: principal units from the next level lie in the kernel of the
lattice-class homomorphism. -/
def chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u : Vn) (hu : (u : 𝒪[L]ˣ) ∈ Vsucc) : Prop :=
    u ∈ (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom
      K L n hVn hmul_error).ker
```

For subgroups `Vn` and `Vsucc` of the units of `𝒪_L` whose underlying sets
are the principal-unit sets of levels `n` and `n + 1`, under the hypothesis
`hmul_error` of M144.121, every `u ∈ Vn` that lies in `Vsucc` is in the
kernel of the homomorphism M144.121. The hypothesis `hVsucc` and the
membership `hu` are used only by the proof, which is not part of this
contribution.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the target lies in
   `Langlands.NYLL.CyclicCohomology`.
2. Replace `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescope and the
   statement are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line, and the line
   breaks are otherwise those of the source. The source proof is omitted:
   this contribution publishes the proposition target, and its proof is
   separate work.
3. Keep the source `omit` line, and add
   `set_option linter.unusedVariables false in` after it. Without the
   option, Lean reports unused-variable warnings for exactly `hVsucc` and
   `hu`, because the statement does not mention them; they are kept so that
   the target has the source telescope.
4. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorem.
5. Replace the three source imports by the companion module
   `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.Definitions`.
6. Keep the source context of lines 1626–1640 and 2296–2297; omit the
   definition M144.121 (ported in the companion module) and the other
   declarations of the source file.
7. No helper declaration or instance is added.

This is an exact source statement as a named proposition, without a
published proof. It discharges no host Herbrand-quotient, class-formation,
Tate or reciprocity target.

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
