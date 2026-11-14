# NYLL recursive lifting on the normal-basis principal-unit filtration: statements

Worker 111 adapts M155.002 and M155.003 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisRecursiveLifting.lean`
(file SHA-256
`13df216489f5c1bc7e91f4016a64eaefeca244394bca621ec5c38a06f4657a08`).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Unit | Original declaration in `LocalClassFieldTheory` | Source lines (docstring through proof; statement) | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M155.002 | `exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNorm` | 53–147; 56–62 | `exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNormStatement` |
| M155.003 | `exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOne` | 149–245; 152–160 | `exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOneStatement` |

## Meaning

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with
`L` carrying the valuation extending that of `K`, `𝒪[L]` integral over `𝒪[K]`
and finite as an `𝒪[K]`-module. Both propositions first install, with
`letI`, the actual action of `Gal(L/K)` on the integer units `𝒪[L]ˣ`
(`galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L`). Write
`U_n` for `chosenNormalBasisPrincipalUnitSet K L n`, the set of integer
units `u` such that `u - 1`, viewed in `L`, lies in
`chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)`.

- M155.002 (recursive `H⁰` lifting): there is `c : Nat` such that for every
  `n ≥ c` and every `a ∈ U_n` fixed by every `sigma : Gal(L/K)`, there is
  `b ∈ U_n` with `a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b`, the product of the
  Galois conjugates of `b`.
- M155.003 (recursive `H⁻¹` lifting): for `g : Gal(L/K)` such that every
  `sigma : Gal(L/K)` lies in `Subgroup.zpowers g`, there is `c : Nat` such
  that for every `n ≥ c` and every `a ∈ U_n` of Tate norm `1`, there is
  `b ∈ U_n` with `a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b`, that is
  `a = g • b * b⁻¹`.

## Telescopes

The universe is `u` (source line 28). The source theorems take their
parameters from the section `variable` command at lines 34–40; both
theorem statements mention `K` and `L`, so every instance binder of that
command is included. The adapted definitions write this telescope
explicitly, in the source order and binder kinds:

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
```

The only `omit` in the source (line 42) applies to the private helper at
line 43 and not to these theorems. M155.002 has no further binders.
M155.003 then has the theorem's own explicit binders
`(g : Gal(L/K)) (hgen : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)`.
The bodies, including the leading
`letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L`,
are copied verbatim from source lines 57–62 and 155–160.
The hypothesis `hgen` does not occur in the M155.003 proposition; it is
retained as in the source, and `set_option linter.unusedVariables false in`
is applied to that one definition to silence the linter. This option does not
change the proposition.

## Reused declarations

- `Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`
  (M140.003), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions`,
  the namespaced adaptation of the source's declaration of the same name.
- `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet`
  (M144.059), from
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions`,
  the namespaced adaptation of the source's
  `CyclicCohomology.chosenNormalBasisPrincipalUnitSet`.
- `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm`
  and `sigmaMinusOne` (M113.001, M113.002), from
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`.
  `tateNorm` uses the `Fintype (Gal(L / K))` instance Mathlib derives from
  `FiniteDimensional K L`.
- Mathlib's `IsNonarchimedeanLocalField`, from
  `Mathlib.NumberTheory.LocalField.Basic`; `IsGalois`, `Module.Finite`,
  `Valuation.HasExtension`, `IsIntegralClosure`, `Subgroup.zpowers` and the
  `Gal(L/K)` and `𝒪[K]` notations come from Mathlib through these imports.

The source's `open CyclicCohomology` (line 20) and
`open CyclicCohomology.ProfiniteCohomology.Herbrand` (line 32) are written
with their full `Langlands.NYLL` names, so the targets use the same
unqualified names as the source. `open scoped ValuativeRel` (line 30) is
retained for the `𝒪[K]` notation.

## Modifications

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`.
- Each theorem becomes a `Prop`-valued `def` with the suffix `Statement`
  whose body is exactly the source statement; the source proofs (which use
  the private helper at line 43, the one-step lifting theorems, the
  convergence of correction products and the M151 recursive sequences) are
  not ported here. Proofs of these targets are separate `lean.proof@1` work.
- The section-variable telescope is written as explicit binders on each
  definition, so that no instance binder is dropped.
- The source imports `...ClassFormation.FilteredLiftingSequence` and
  `...ClassFormation.NormalBasisGradedLifting` are replaced by the three
  published Library modules above and Mathlib's local-field module, which
  supply every constant the targets mention.
- `open LocalFieldTheory` (line 22) and `open Filter IsNonarchimedeanLocalField`
  (line 31) are omitted: the two targets use no name from these namespaces,
  and neither namespace declares scoped instances or notation used here.
- The private helper `filteredCorrectionProduct_eq_chosenNormalBasisProduct`
  (lines 42–51) is omitted; it occurs only in the source proofs.
- Docstrings are rewritten to describe each proposition and name its unit.

No hypothesis is added or removed, no proof is supplied and no instance is
declared; the integer-unit action is installed locally by `letI`, as in the
source. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. These statements
prove no class-formation or reciprocity theorem.
