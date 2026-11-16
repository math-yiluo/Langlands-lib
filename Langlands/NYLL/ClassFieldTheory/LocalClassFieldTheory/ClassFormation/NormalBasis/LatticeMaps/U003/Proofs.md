# The lattice basis vectors are the normal-basis vectors

This module proves
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_apply`,
the proof phase of M152.003 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m152).
Its type is exactly the target
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_applyStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem chosenNormalBasisIntegerLatticeBasis_apply (σ : Gal(L/K)) :
    chosenNormalBasisIntegerLatticeBasis_applyStatement K L σ
```

The section variables are those of the target module, so the parameters are
the target's parameters in the target's order: a finite Galois extension
`L/K` of fields in one universe `u`, with a `ValuativeRel K` instance, and a
Galois element `σ`. No topology or local-field hypothesis is assumed. The
target unfolds to

```lean
((chosenNormalBasisIntegerLatticeBasis K L σ :
  chosenNormalBasisIntegerLattice K L) : L) = IsGalois.normalBasis K L σ
```

that is, the `σ`-th vector of the `𝒪[K]`-basis of the normal-basis lattice,
viewed in `L`, is the `σ`-th vector of Mathlib's normal basis. No hypothesis
is added.

## Implemented proof

```lean
  Module.Basis.restrictScalars_apply 𝒪[K] (IsGalois.normalBasis K L) σ
```

Mathlib's `Module.Basis.restrictScalars_apply R b i` states
`(b.restrictScalars R i : M) = b i`, where `b.restrictScalars R` is the
`R`-basis of `Submodule.span R (Set.range b)` given by the vectors of `b`.
Here `b = IsGalois.normalBasis K L`, `R = 𝒪[K]` and `i = σ`. The term has
the target's type up to definitional unfolding:

1. The published definition `chosenNormalBasisIntegerLatticeBasis K L`
   (M152.002, module `...NormalBasis.IntegerLatticeBasis`) is
   `((IsGalois.normalBasis K L).restrictScalars 𝒪[K]).map (LinearEquiv.ofEq _ _ h)`,
   where `h` is the published theorem
   `span_normalBasis_eq_chosenNormalBasisIntegerLattice K L` identifying the
   span with `chosenNormalBasisIntegerLattice K L`.
2. Mathlib's `Module.Basis.map` satisfies `(b'.map f) σ = f (b' σ)`
   definitionally, and the coercion to `L` of `LinearEquiv.ofEq p q h y` is
   definitionally the coercion of `y` (Mathlib proves
   `LinearEquiv.coe_ofEq_apply` by `rfl`).
3. So the target's left side reduces to
   `(((IsGalois.normalBasis K L).restrictScalars 𝒪[K] σ : _) : L)`, the left
   side of the Mathlib lemma, and the right sides agree.

No auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean#L53-L58):
the docstring at line 53, the `@[simp]` attribute at line 54 and the theorem
at lines 55–58 (telescope and conclusion at 55–57, tactic at 58), under the
section variables at lines 28–29; the task's unit range 55–65 ends before the
next declaration at 66. The retained original file has SHA-256
`affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`. The
source proof is

```lean
  simp [chosenNormalBasisIntegerLatticeBasis, LinearEquiv.coe_ofEq_apply]
```

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_apply` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_apply` |
| Its statement | `chosenNormalBasisIntegerLatticeBasis_applyStatement K L σ` |
| `simp` with `LinearEquiv.coe_ofEq_apply` (and Mathlib's `@[simp]` lemma `Module.Basis.restrictScalars_apply`) | Term-mode `Module.Basis.restrictScalars_apply` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; keep the source section variables; give the theorem the
target applied to its parameters as its type; omit the `@[simp]` attribute,
because the theorem's type is a `Statement` application. The source `simp`
call does not close the goal in this setting. In the published basis
definition the equality argument of `LinearEquiv.ofEq` is the published
theorem `span_normalBasis_eq_chosenNormalBasisIntegerLattice`, whose type is
the closed `Statement` definition rather than the bare equation of the
source. In development checks, the source `simp` call stops at the goal
`↑((LinearEquiv.ofEq _ _ h) ((IsGalois.normalBasis K L).restrictScalars 𝒪[K] σ)) = IsGalois.normalBasis K L σ`
without using `LinearEquiv.coe_ofEq_apply`, and
`rw [chosenNormalBasisIntegerLatticeBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply]`
finds no instance of the last pattern, with Lean's note that the goal is not
type-correct at `implicit` transparency because that argument has the
`Statement` type where the equation is expected. The proof is therefore the
term-mode application of Mathlib's `Module.Basis.restrictScalars_apply`
described above, which is checked by definitional unfolding instead of
rewriting. Import only the target module; omit the source
`noncomputable section` and all other source declarations. The name,
docstring (rewrapped) and telescope are unchanged. The partition records no
patch10 change to this module.

## Imports

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Statements`
  supplies the target and, through `...NormalBasis.LatticeMaps.Definitions`
  and `...NormalBasis.IntegerLatticeBasis`, the basis
  `chosenNormalBasisIntegerLatticeBasis`, the lattice
  `chosenNormalBasisIntegerLattice` and Mathlib's normal basis and
  `Module.Basis.restrictScalars`.

This module and everything it imports are left unchanged.

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

This module proves only M152.003; the Galois-action identity M152.024 and
the coordinate rule M152.027 are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
