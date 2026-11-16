# Normal-basis lattice coordinates under the Galois action

This module proves
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup`,
the proof phase of M152.027 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m152).
Its type is exactly the target
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup
    (τ σ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement K L τ σ x
```

The section variables and the `omit` line are those of the target module, so
the parameters are the target's parameters in the target's order: a finite
Galois extension `L/K` of fields in one universe `u`, with a
`ValuativeRel K` instance, Galois elements `τ`, `σ` and an element `x` of the
normal-basis lattice. The topology and local-field instances of the section
are omitted, as in the target. The target unfolds to

```lean
(chosenNormalBasisIntegerLatticeBasis K L).equivFun
    (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) σ =
  (chosenNormalBasisIntegerLatticeBasis K L).equivFun x (τ⁻¹ * σ)
```

that is, in the lattice basis, the `σ`-coordinate of `τ x` is the
`τ⁻¹ σ`-coordinate of `x`. No hypothesis is added.

## Implemented proof

```lean
  unfold chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement
  have happly : ∀ ρ : Gal(L/K),
      ((chosenNormalBasisIntegerLatticeBasis K L ρ :
        chosenNormalBasisIntegerLattice K L) : L) = IsGalois.normalBasis K L ρ :=
    fun ρ => Module.Basis.restrictScalars_apply 𝒪[K] (IsGalois.normalBasis K L) ρ
  have hcoe : ∀ y : chosenNormalBasisIntegerLattice K L,
      ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ y :
        chosenNormalBasisIntegerLattice K L) : L) = τ (y : L) :=
    fun _ => rfl
  let b := chosenNormalBasisIntegerLatticeBasis K L
  let f := galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ
  let e : Gal(L / K) ≃ Gal(L / K) := Equiv.mulLeft τ⁻¹
  have hbmap : b.map f = b.reindex e := by
    ext ρ
    rw [Module.Basis.map_apply, Module.Basis.reindex_apply]
    have he : e.symm ρ = τ * ρ := by
      simp [e]
    rw [he]
    simp only [f, b, hcoe, happly]
    rw [IsGalois.normalBasis_apply (K := K) (L := L) (τ * ρ),
      IsGalois.normalBasis_apply (K := K) (L := L) ρ]
    rfl
  have hcoord (ρ : Gal(L / K)) :
      b.equivFun (f x) (τ * ρ) = b.equivFun x ρ := by
    calc
      b.equivFun (f x) (τ * ρ) =
          (b.reindex e).equivFun (f x) ρ := by
            rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
              Module.Basis.repr_reindex_apply]
            simp [e]
      _ = (b.map f).equivFun (f x) ρ := by rw [hbmap]
      _ = b.equivFun x ρ := by
        rw [Module.Basis.map_equivFun]
        simp [f]
  simpa using hcoord (τ⁻¹ * σ)
```

1. `unfold` exposes the coordinate equation.
2. Two local hypotheses record the M152.003 and M152.024 identities, whose
   proofs are not yet in the Library:
   - `happly`: the lattice basis vector at `ρ`, viewed in `L`, is
     `IsGalois.normalBasis K L ρ`. It is proved as in the M152.003 proof of
     the same task: Mathlib's `Module.Basis.restrictScalars_apply` applied to
     the normal basis over `𝒪[K]`, which has this type after unfolding the
     published basis `chosenNormalBasisIntegerLatticeBasis` (M152.002, the
     restricted-scalars normal basis mapped along `LinearEquiv.ofEq`).
   - `hcoe`: the lattice action of `τ`, viewed in `L`, is `τ` on `L`. It is
     proved by `rfl`, as in the M152.024 proof of the same task, because the
     published `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`
     (M152.023) has forward function `fun y => ⟨τ (y : L), _⟩`.
3. With `b` the lattice basis, `f` the action of `τ` and `e` the
   left-multiplication bijection `ρ ↦ τ⁻¹ ρ` of `Gal(L/K)`, the claim
   `hbmap : b.map f = b.reindex e` says that `τ` permutes the basis vectors.
   After `ext ρ` and Mathlib's `Module.Basis.map_apply` and
   `Module.Basis.reindex_apply`, the two vectors are `f (b ρ)` and
   `b (e.symm ρ)`; `simp` shows `e.symm ρ = τ * ρ`. Rewriting with `he` and
   `simp only` with `hcoe` and `happly` reduces the claim to
   `τ (IsGalois.normalBasis K L ρ) = IsGalois.normalBasis K L (τ * ρ)`.
   Mathlib's `IsGalois.normalBasis_apply`, which writes
   `IsGalois.normalBasis K L g` as `g (IsGalois.normalBasis K L 1)`, applied
   at `τ * ρ` and at `ρ`, turns this into
   `τ (ρ (IsGalois.normalBasis K L 1)) = (τ * ρ) (IsGalois.normalBasis K L 1)`,
   which holds by `rfl` because multiplication in `Gal(L/K)` is composition.
4. `hcoord ρ : b.equivFun (f x) (τ * ρ) = b.equivFun x ρ` is a three-step
   calculation. First, Mathlib's `Module.Basis.equivFun_apply` and
   `Module.Basis.repr_reindex_apply` express the reindexed coordinate at
   `ρ` as the original coordinate at `e.symm ρ = τ * ρ` (by `simp [e]`).
   Second, `hbmap` replaces the reindexed basis by the mapped one. Third,
   Mathlib's `Module.Basis.map_equivFun` writes the mapped coordinates as
   `f.symm.trans b.equivFun`, and `simp [f]` cancels `f.symm (f x) = x`.
5. Finally `hcoord (τ⁻¹ * σ)` gives the target after `simpa` simplifies
   `τ * (τ⁻¹ * σ)` to `σ`.

No auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean#L459-L493):
the `omit` line at line 459, the docstring at lines 460–461 and the theorem
at lines 462–493 (telescope and conclusion at 462–466, tactics at 467–493),
under the section variables at lines 28–29 and 62; the task's unit range
462–495 ends before the next declaration at 496. The retained original file
has SHA-256
`affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`. The
source tactics are the displayed proof from `let b := ...` on, except that
the source `simp only` step at lines 476–477 reads

```lean
    simp only [f, b, galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe,
      chosenNormalBasisIntegerLatticeBasis_apply]
```

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup` |
| Its statement | `chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement K L τ σ x` |
| Used `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe` (M152.024) | Local hypothesis `hcoe`, proved by `rfl` |
| Used `chosenNormalBasisIntegerLatticeBasis_apply` (M152.003) | Local hypothesis `happly`, proved by Mathlib's `Module.Basis.restrictScalars_apply` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; keep the source section variables and `omit` line; give
the theorem the target applied to its parameters as its type and unfold it
at the start of the proof; add the local hypotheses `happly` and `hcoe`
stating M152.003 and M152.024 for this proof, because their proofs are not
yet in the Library, and use them in place of those two theorems in the
`simp only` step. `happly` is not proved by the source M152.003 `simp`
call, which does not close that goal over the published basis definition
(see the M152.003 proof's Markdown in
`../U003/Proofs.md`); it uses the Mathlib lemma instead. All other source
tactics are unchanged. Import only the target module; omit the source
`noncomputable section` and all other source declarations. The name,
docstring and telescope are unchanged. The partition records no patch10
change to this module.

## Imports

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Statements`
  supplies the target and, through `...NormalBasis.LatticeMaps.Definitions`
  and `...NormalBasis.IntegerLatticeBasis`, the lattice basis
  `chosenNormalBasisIntegerLatticeBasis`, the action
  `galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`, the lattice
  `chosenNormalBasisIntegerLattice` and Mathlib's normal basis and basis
  API.

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

This module proves only M152.027; the Galois stability of the lattice
uniformizer submodule (M152.028) is a separate unit.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
