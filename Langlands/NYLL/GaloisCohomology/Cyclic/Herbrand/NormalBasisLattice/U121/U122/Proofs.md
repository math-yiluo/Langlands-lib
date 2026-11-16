# The lattice successive-quotient map kills the next level

This module proves
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ`,
the proof phase of M144.122 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m144).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
theorem chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ
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
    (u : Vn) (hu : (u : 𝒪[L]ˣ) ∈ Vsucc) :
    chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement
      K L hVn hVsucc hmul_error u hu
```

The section variables and the `omit` line are those of the target module, so
the theorem's parameters are the target's parameters in the target's order:
a finite Galois extension `L/K` of fields in one universe `u`, with valuative
relations on both, a topology on `K` making it a nonarchimedean local field;
the instance `Valuation.HasExtension` is omitted, as in the target. The
explicit hypotheses are the target's: subgroups `Vn`, `Vsucc` of `𝒪[L]ˣ`
whose carriers are the published sets `chosenNormalBasisPrincipalUnitSet K L n`
and `chosenNormalBasisPrincipalUnitSet K L (n + 1)`, the multiplicative error
condition `hmul_error` at level `n`, an element `u : Vn` and the membership
`hu` of `u` in `Vsucc`. The target unfolds to

```lean
u ∈ (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom
  K L n hVn hmul_error).ker
```

that is, the homomorphism `Vn → π_K^n M/π_K^(n+1) M` (with the additive
quotient viewed multiplicatively) kills every element of `Vn` lying in
`Vsucc`. No hypothesis is added.

## Implemented proof

```lean
  unfold chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement
  rw [MonoidHom.mem_ker]
  have hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    exact hVn ▸ u.2
  have hu_succ : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
    exact hVsucc ▸ hu
  have hzero :
      chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 :=
    (chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff
      (K := K) (L := L) (u : 𝒪[L]ˣ) hu_n).2 hu_succ
  change Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n) = 1
  simpa using congrArg Multiplicative.ofAdd hzero
```

1. `unfold` exposes the kernel membership, and Mathlib's `MonoidHom.mem_ker`
   turns it into the equation
   `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom K L n hVn hmul_error u = 1`.
2. Transporting `u.2 : (u : 𝒪[L]ˣ) ∈ Vn` along `hVn` gives
   `hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n`, and
   transporting `hu` along `hVsucc` gives the level-`(n + 1)` membership
   `hu_succ`.
3. The published theorem
   `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff`
   (M144.103), whose type
   `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iffStatement K L u hu_n`
   unfolds to
   `chosenNormalBasisPrincipalUnitLatticeClass K L n u hu_n = 0 ↔ u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1)`,
   is used in its reverse direction with `hu_succ`: the lattice class of `u`
   is zero.
4. The published definition of
   `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom` (M144.121) sends `u`
   to `Multiplicative.ofAdd` of the lattice class of `(u : 𝒪[L]ˣ)`, with a
   membership proof built from `hVn` and `u.2`. By proof irrelevance this
   is definitionally the class with the proof `hu_n`, so `change` states the
   goal as `Multiplicative.ofAdd (class) = 1`.
5. `congrArg Multiplicative.ofAdd hzero` gives
   `Multiplicative.ofAdd (class) = Multiplicative.ofAdd 0`, and `simpa`
   rewrites `Multiplicative.ofAdd 0` to `1` (Mathlib's `ofAdd_zero`) to close
   the goal.

No auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L2159-L2187):
the `omit` line at lines 2159–2160, the docstring at line 2161 and the
theorem at lines 2162–2187 (telescope and conclusion at 2162–2175, tactics at
2176–2187); the task's unit range 2162–2191 ends before the next declaration
at 2192. The retained original file has SHA-256
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`. The
source tactics at lines 2176–2187 are, verbatim, the displayed proof without
its first line `unfold ...`.

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ` | `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ` |
| Its statement | `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succStatement K L hVn hVsucc hmul_error u hu` |
| Used `CyclicCohomology.chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff` | Published `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff`, by `.2` as in the source |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; keep the source section variables and `omit` line; give
the theorem the target applied to its parameters as its type and unfold it
at the start of the proof; replace the source imports by the two imports
below; omit the source `noncomputable section` and all other source
declarations. The name, docstring (rewrapped), telescope and all source
tactics are unchanged; the published theorem is applied through `.2`
exactly as in the source, so its `Statement` type needs no adaptation. The
partition records no patch10 change to this module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U121.Statements`
  supplies the target and, through `...NormalBasisLattice.U121.Definitions`,
  the homomorphism `chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom`, the
  lattice class `chosenNormalBasisPrincipalUnitLatticeClass`, the sets
  `chosenNormalBasisPrincipalUnitSet` and the lattice quotient.
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U103.Proofs`
  is the published proof module of
  `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff`. The definitions
  module already imports it; it is imported here explicitly because the
  proof uses it.

Both modules and everything they import are left unchanged.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", released under Apache-2.0. The Lean file carries the dated
modification record. The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker
750 adapted this proof directly from the pinned original. The statement is
Worker 5264's, used unchanged.

This module proves only M144.122; the induced map on `Vn/Vsucc` (M144.123)
and its properties are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
