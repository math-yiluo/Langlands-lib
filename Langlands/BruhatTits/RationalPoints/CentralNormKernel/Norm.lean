import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.CentralAlgebra
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.SpectralBlock

/-! # Eigenvalues of central norm-kernel points have spectral norm one

Let `F` be a nonarchimedean local field, normed by `LocalGalois.localNormedField`, and `ρ` a
matrix representation of a group scheme `M` over `F`. For a central rational point `z` in the
rational common norm kernel, every eigenvalue `c` of `ρ(z)` in the algebraic closure has spectral
norm `1`: an `F`-rational idempotent polynomial `π` in `ρ(z)` gives the block-determinant
character `g ↦ det (ρ(g) π + (1 - π))` of `M`, whose value at `z` has norm one, and that norm is a
positive power of the spectral norm of `c`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix
open Langlands.GroupScheme Langlands.GroupScheme.CentralIntersection

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

section Characters

variable {F : Type u} [Field F]

variable {M : GroupScheme (Spec (CommRingCat.of F))} {N : Type} [Fintype N] [DecidableEq N]

/-- The block-determinant character of an idempotent polynomial in the matrix of a central
point, as a rational character. -/
def centralBlockCharacter (ρ : MatrixRepresentation M N) {z : rationalPoints M}
    (hz : z ∈ GroupScheme.schemeCenterPoints M) (P : F[X])
    (hP : IsIdempotentElem (aeval (ρ.rationalMatrix z : Matrix N N F) P)) :
    rationalCharacters M :=
  Additive.ofMul (blockCharacter (ρ := ρ) hP fun T g => commute_scalarMap_of_mem ρ
    (Algebra.adjoin_mono (Set.singleton_subset_iff.2 (rationalMatrix_mem_centralMatrices ρ hz))
      (aeval_mem_adjoin_singleton F _)) T g)

theorem rationalCharacterEval_centralBlockCharacter (ρ : MatrixRepresentation M N)
    {z : rationalPoints M} (hz : z ∈ GroupScheme.schemeCenterPoints M) (P : F[X])
    (hP : IsIdempotentElem (aeval (ρ.rationalMatrix z : Matrix N N F) P)) (x : rationalPoints M) :
    (rationalCharacterEval (centralBlockCharacter ρ hz P hP) x : F) =
      ((ρ.rationalMatrix x : Matrix N N F) * aeval (ρ.rationalMatrix z : Matrix N N F) P +
        (1 - aeval (ρ.rationalMatrix z : Matrix N N F) P)).det := by
  rw [rationalCharacterEval_val, characterEval_apply, ← ΓSpecIso_det_blockMatrix]
  congr 1
  change (Gm.pointsEquiv _ _ (x ≫ (blockCharacter hP _).hom.hom)).val = _
  rw [comp_blockCharacter, blockDetPoints_val]

end Characters

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A unit of trivial normalized absolute value has norm one for the local-field norm. -/
theorem norm_eq_one_of_fieldNormUnits_eq_one (a : Fˣ) (h : Plancherel.fieldNormUnits F a = 1) :
    letI := LocalGalois.localNormedField F
    ‖(a : F)‖ = 1 := by
  let := LocalGalois.localNormedField F
  have hmem : a ∈ FML.unitGroup F := by
    rw [← Plancherel.fieldNormUnits_ker]
    exact h
  have hv : ValuativeRel.valuation F (a : F) = 1 := by
    simpa only [FML.unitGroup, Valuation.mem_unitGroup_iff] using hmem
  have h1 := (LocalGalois.localNormedField_le F (a : F) 1).2 (by rw [hv, map_one])
  have h2 := (LocalGalois.localNormedField_le F 1 (a : F)).2 (by rw [hv, map_one])
  rw [norm_one] at h1 h2
  exact le_antisymm h1 h2

variable {M : GroupScheme (Spec (CommRingCat.of F))} {N : Type} [Fintype N] [DecidableEq N]

/-- **Spectral norm of eigenvalues.** Every eigenvalue of the matrix of a central point of the
norm kernel has spectral norm one. -/
theorem spectralNorm_eq_one_of_mem_normKernel (ρ : MatrixRepresentation M N)
    {z : rationalPoints M} (hz : z ∈ GroupScheme.schemeCenterPoints M)
    (hK : z ∈ Plancherel.rationalCommonNormKernel M) {c : AlgebraicClosure F}
    (hc : ((ρ.rationalMatrix z : Matrix N N F).charpoly.map
      (algebraMap F (AlgebraicClosure F))).IsRoot c) :
    letI := LocalGalois.localNormedField F
    spectralNorm F (AlgebraicClosure F) c = 1 := by
  let := LocalGalois.localNormedField F
  have : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  have : CompleteSpace F := LocalGalois.localNormedField_complete F
  obtain ⟨P, hP, b, hb, hnorm⟩ := exists_blockProjector_spectralNorm _ hc
  have hχ := (Plancherel.mem_rationalCommonNormKernel M z).1 hK (centralBlockCharacter ρ hz P hP)
  have h1 := norm_eq_one_of_fieldNormUnits_eq_one _ hχ
  rw [rationalCharacterEval_centralBlockCharacter] at h1
  rw [h1] at hnorm
  exact (pow_eq_one_iff_of_nonneg (spectralNorm_nonneg c) (by omega)).1 hnorm.symm

end LocalField

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
