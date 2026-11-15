/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions

/-!
# Targets: the normal-basis lattice basis and the Galois action on its coordinates

Modified by Worker 5264, 15 November 2026: state the source theorems M152.003
`chosenNormalBasisIntegerLatticeBasis_apply`, M152.024
`galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe` and M152.027
`chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup` of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions with the source section variables and `omit` lines. Prefix the
namespace with `Langlands.NYLL`, append `Statement` to each name, omit the
proofs, the `@[simp]` attributes and the rest of the source file, and import
the module of this port that defines the Galois action instead of the source
imports. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/


namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Target: the integral lattice basis has the same underlying vectors as the
chosen normal basis. -/
def chosenNormalBasisIntegerLatticeBasis_applyStatement (σ : Gal(L/K)) : Prop :=
    ((chosenNormalBasisIntegerLatticeBasis K L σ :
      chosenNormalBasisIntegerLattice K L) : L) = IsGalois.normalBasis K L σ

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Target: the restricted lattice equivalence agrees with the ambient Galois
action. -/
def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coeStatement
    (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) : Prop :=
    ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x :
      chosenNormalBasisIntegerLattice K L) : L) = τ (x : L)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Target: normal-basis lattice coordinates obey the left-regular rule before
the inverse-index reindexing. -/
def chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroupStatement
    (τ σ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) : Prop :=
    (chosenNormalBasisIntegerLatticeBasis K L).equivFun
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) σ =
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun x (τ⁻¹ * σ)

end GradedCoordinates

end
end Langlands.NYLL.LocalClassFieldTheory
