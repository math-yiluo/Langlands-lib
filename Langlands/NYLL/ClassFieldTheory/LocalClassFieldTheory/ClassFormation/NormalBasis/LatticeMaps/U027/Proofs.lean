/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M152.027 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 462–495. Add the Langlands.NYLL
namespace prefix, keep the source section variables and `omit` line, and give
the theorem the published target applied to its parameters as its type,
unfolded at the start of the proof. The source `simp only` step uses M152.003
`chosenNormalBasisIntegerLatticeBasis_apply` and M152.024
`galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe`, whose
proofs are not yet in the Library: this proof states those two identities as
local hypotheses `happly` and `hcoe`, proved as in the M152.003 and M152.024
proofs of the same task (Mathlib's `Module.Basis.restrictScalars_apply`, and
`rfl`), and uses them in that step. The remaining tactics are unchanged. Import only the target module. Omit the source
noncomputable section and all other source declarations. See the paired
Markdown; the original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Statements

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Normal-basis lattice coordinates obey the left-regular rule before the
inverse-index reindexing. -/
theorem chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup
    (τ σ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement K L τ σ x := by
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

end GradedCoordinates

end Langlands.NYLL.LocalClassFieldTheory
