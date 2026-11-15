# NYLL M144.121: the homomorphism from a principal-unit level to the successive lattice quotient

The paired Lean file adapts one definition of Naganori
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

| Unit | Source definition after `CyclicCohomology.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.CyclicCohomology.` |
| --- | --- | --- | --- | --- | --- |
| M144.121 | `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom` | 2120–2121 | 2122–2132 | 2133–2157 | `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom` |

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

The definition does not use the instance
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`
of the `variable` command, and Lean does not include it. The elaborated
telescope, printed with `#check` in the project Lean service, is
`(K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
[IsGalois K L] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K] [ValuativeRel L]`, followed by the binders
shown below.

The published NYLL declarations used, all in `Langlands.NYLL.CyclicCohomology`, are the
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
`u - 1` in that quotient (M144.102, in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U102.Definitions`). The embedded proofs also use the published theorems
`chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff` (M144.103, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U103.Proofs`) and
`chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add` (M144.106, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U106.Proofs`). Their types are the published targets
`chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iffStatement K L u hu`,
the proposition
`chosenNormalBasisPrincipalUnitLatticeClass K L n u hu = 0 ↔ u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1)`,
and
`chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_addStatement K L hmul_error u v hu hv huv`,
the equation that the class of `u * v` is the sum of the classes of `u` and
`v`, both in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.Statements`. Mathlib supplies `Subgroup`, the
units `𝒪[L]ˣ`, `MonoidHom`, `Multiplicative` with `Multiplicative.ofAdd`,
`Units.val_one`, `sub_self`, `ZeroMemClass.coe_zero`, `Submodule.zero_mem`
and `congrArg`.

The other declarations of the source file are not part of this module. The
statement of the theorem M144.122 is in the companion module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.Statements` of this contribution.

## Definition

```lean
/-- The map `u ↦ u - 1` from a subgroup `Vn = V^n` to the additive
successive quotient, viewed multiplicatively on the target. -/
def chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom (n : Nat)
    {Vn : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    Vn →* Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) where
  toFun u :=
    Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
        (by
          exact hVn ▸ u.2))
  map_one' := by
    change chosenNormalBasisPrincipalUnitLatticeClass K L n
      (1 : 𝒪[L]ˣ) (by exact hVn ▸ (1 : Vn).2) = 0
    have hzero_iff : ∀ (w : 𝒪[L]ˣ) (hw : w ∈ chosenNormalBasisPrincipalUnitSet K L n),
        chosenNormalBasisPrincipalUnitLatticeClass K L n w hw = 0 ↔
          w ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) :=
      fun w hw => chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff K L w hw
    rw [hzero_iff]
    change ((((1 : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L)
    rw [Units.val_one, sub_self, ZeroMemClass.coe_zero]
    exact Submodule.zero_mem _
  map_mul' := by
    intro u v
    have hu : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ u.2
    have hv : (v : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ v.2
    have huv : ((u * v : Vn) : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ (u * v).2
    have hclass :=
      chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add
        (K := K) (L := L) hmul_error (u : 𝒪[L]ˣ) (v : 𝒪[L]ˣ) hu hv huv
    simpa using congrArg Multiplicative.ofAdd hclass
```

For a subgroup `Vn` of the units of `𝒪_L` whose underlying set is the
level-`n` principal-unit set, and under the hypothesis `hmul_error` that
`(uv - 1) - ((u - 1) + (v - 1))` lies in the `(n + 1)`-st dilate of the
lattice for all `u, v` of level `n`, the definition is the homomorphism
`Vn → Multiplicative (M_n / M_(n+1))` sending `u` to the class of `u - 1`.
The `map_one'` block proves that the class of `1 - 1 = 0` is zero, and the
`map_mul'` block derives multiplicativity from M144.106.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom`.
2. In the `map_one'` proof, the source line 2141
   `rw [chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff]` is
   replaced by a local hypothesis `hzero_iff`, stating for every
   `w : 𝒪[L]ˣ` and `hw : w ∈ chosenNormalBasisPrincipalUnitSet K L n` the
   equivalence
   `chosenNormalBasisPrincipalUnitLatticeClass K L n w hw = 0 ↔ w ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1)`,
   proved by the published M144.103, followed by `rw [hzero_iff]`. The
   published theorem has the Prop-valued type
   `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iffStatement K L w hw`,
   which `rw` does not unfold; the local hypothesis has exactly the
   equivalence the source rewrites with. The rest of the tactic block is
   unchanged. The change is inside a proof of a proposition, so the
   homomorphism is that of the source.
3. In the `map_mul'` proof, the source line
   `chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add (K := K) (L := L) hmul_error …`
   is kept: `have hclass := …` takes the published Statement type, and
   `congrArg Multiplicative.ofAdd hclass` accepts it because that type
   unfolds to the source equation.
4. Copy the docstring, the binders and the rest of the body verbatim, with
   the source line breaks.
5. Replace the three source imports by the two published modules
   `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U103.Proofs` and `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U106.Proofs`, which import the
   modules of all names listed above, and the source module docstring by a
   description of this module with a modification notice.
6. Keep the source context of lines 1626–1640 and 2296–2297; omit the other
   declarations of the source file.
7. No helper declaration, instance or linter option is added.

This is a definition only. It discharges no host Herbrand-quotient,
class-formation, Tate or reciprocity target.

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
