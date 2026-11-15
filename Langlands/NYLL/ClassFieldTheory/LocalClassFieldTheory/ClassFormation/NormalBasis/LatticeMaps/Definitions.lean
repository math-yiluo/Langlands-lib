/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.IntegerLatticeBasis
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.U007.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U015.Proofs

/-!
# Uniformizer scaling and the Galois action on the normal-basis lattice

Modified by Worker 5264, 15 November 2026: port the source definitions
M152.004 `chosenNormalBasisIntegerLatticeMulPowLinearMap` and M152.023
`galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv` of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 with their source binders,
section variables, docstrings and bodies. Prefix the namespace with
`Langlands.NYLL`, import the three focused published modules above instead of
the four source imports, and omit the other source declarations. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/


namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

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

/-! ### The actual `Gal(L / K)` action and right-regular equivariance -/

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

end GradedCoordinates

end
end Langlands.NYLL.LocalClassFieldTheory
