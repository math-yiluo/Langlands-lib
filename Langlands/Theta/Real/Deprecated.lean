import Langlands.Theta.Real.BigCellOperator
import Langlands.Theta.Real.Intertwiner
import Langlands.Theta.Real.Metaplectic.Basic
import Langlands.Theta.Real.Metaplectic.Defs
import Langlands.Theta.Real.Metaplectic.Gaussian
import Langlands.Theta.Real.Metaplectic.Smooth
import Langlands.Theta.Real.Metaplectic.Unipotent
import Langlands.Theta.Real.Schrodinger
import Langlands.Theta.Real.SchrodingerDeriv
import Langlands.Theta.Real.WeylAlgebra

/-!
# Deprecated names of the real branch

Outside GKT (the archimedean theory, which the book leaves out, preface p. iv). The declarations of
`Langlands/Theta/Real/` are in the name space `Langlands.Theta.Real`, except `RealMetaplecticGroup`
and its name space; the standard symplectic form is `Langlands.stdSymplecticForm`
(`Langlands.LinearAlgebra.Symplectic`). This module provides, for each of them, a deprecated alias
(since 2026-11-23) in the name space `Langlands.Theta`.
-/

noncomputable section

namespace Langlands.Theta

@[deprecated Langlands.Theta.Real.bigCellOp (since := "2026-11-23")]
alias bigCellOp := Langlands.Theta.Real.bigCellOp

@[deprecated Langlands.Theta.Real.bigCellOp_one (since := "2026-11-23")]
alias bigCellOp_one := Langlands.Theta.Real.bigCellOp_one

@[deprecated Langlands.Theta.Real.chirp (since := "2026-11-23")]
alias chirp := Langlands.Theta.Real.chirp

@[deprecated Langlands.Theta.Real.chirp_apply (since := "2026-11-23")]
alias chirp_apply := Langlands.Theta.Real.chirp_apply

@[deprecated Langlands.Theta.Real.chirp_mul (since := "2026-11-23")]
alias chirp_mul := Langlands.Theta.Real.chirp_mul

@[deprecated Langlands.Theta.Real.chirp_zero (since := "2026-11-23")]
alias chirp_zero := Langlands.Theta.Real.chirp_zero

@[deprecated Langlands.Theta.Real.dilation (since := "2026-11-23")]
alias dilation := Langlands.Theta.Real.dilation

@[deprecated Langlands.Theta.Real.dilation_apply (since := "2026-11-23")]
alias dilation_apply := Langlands.Theta.Real.dilation_apply

@[deprecated Langlands.Theta.Real.dilation_mul (since := "2026-11-23")]
alias dilation_mul := Langlands.Theta.Real.dilation_mul

@[deprecated Langlands.Theta.Real.dilation_one (since := "2026-11-23")]
alias dilation_one := Langlands.Theta.Real.dilation_one

@[deprecated Langlands.Theta.Real.instHasSummableGeomSeriesEuclidean (since := "2026-11-23")]
alias instHasSummableGeomSeriesEuclidean := Langlands.Theta.Real.instHasSummableGeomSeriesEuclidean

@[deprecated Langlands.Theta.Real.isUnit_bigCellOp (since := "2026-11-23")]
alias isUnit_bigCellOp := Langlands.Theta.Real.isUnit_bigCellOp

@[deprecated Langlands.Theta.Real.isUnit_chirp (since := "2026-11-23")]
alias isUnit_chirp := Langlands.Theta.Real.isUnit_chirp

@[deprecated Langlands.Theta.Real.isUnit_dilation (since := "2026-11-23")]
alias isUnit_dilation := Langlands.Theta.Real.isUnit_dilation

@[deprecated Langlands.Theta.Real.Intertwines (since := "2026-11-23")]
alias Intertwines := Langlands.Theta.Real.Intertwines

@[deprecated Langlands.Theta.Real.Intertwines.comm (since := "2026-11-23")]
alias Intertwines.comm := Langlands.Theta.Real.Intertwines.comm

@[deprecated Langlands.Theta.Real.Intertwines.comm_rhoFun (since := "2026-11-23")]
alias Intertwines.comm_rhoFun := Langlands.Theta.Real.Intertwines.comm_rhoFun

@[deprecated Langlands.Theta.Real.Intertwines.comm_schrodingerDeriv (since := "2026-11-23")]
alias Intertwines.comm_schrodingerDeriv := Langlands.Theta.Real.Intertwines.comm_schrodingerDeriv

@[deprecated Langlands.Theta.Real.Intertwines.continuous (since := "2026-11-23")]
alias Intertwines.continuous := Langlands.Theta.Real.Intertwines.continuous

@[deprecated Langlands.Theta.Real.Intertwines.exists_eq_smul (since := "2026-11-23")]
alias Intertwines.exists_eq_smul := Langlands.Theta.Real.Intertwines.exists_eq_smul

@[deprecated Langlands.Theta.Real.Intertwines.inner (since := "2026-11-23")]
alias Intertwines.inner := Langlands.Theta.Real.Intertwines.inner

@[deprecated Langlands.Theta.Real.Intertwines.mk (since := "2026-11-23")]
alias Intertwines.mk := Langlands.Theta.Real.Intertwines.mk

@[deprecated Langlands.Theta.Real.Intertwines.norm_toLp (since := "2026-11-23")]
alias Intertwines.norm_toLp := Langlands.Theta.Real.Intertwines.norm_toLp

@[deprecated Langlands.Theta.Real.Intertwines.of_rhoFun (since := "2026-11-23")]
alias Intertwines.of_rhoFun := Langlands.Theta.Real.Intertwines.of_rhoFun

@[deprecated Langlands.Theta.Real.oscillatorDeriv_mem_weylAlgebra (since := "2026-11-23")]
alias oscillatorDeriv_mem_weylAlgebra := Langlands.Theta.Real.oscillatorDeriv_mem_weylAlgebra

@[deprecated Langlands.Theta.Real.automorphyDet_one (since := "2026-11-23")]
alias automorphyDet_one := Langlands.Theta.Real.automorphyDet_one

@[deprecated Langlands.Theta.Real.fderiv_gaussianVector (since := "2026-11-23")]
alias fderiv_gaussianVector := Langlands.Theta.Real.fderiv_gaussianVector

@[deprecated Langlands.Theta.Real.gaussianVector (since := "2026-11-23")]
alias gaussianVector := Langlands.Theta.Real.gaussianVector

@[deprecated Langlands.Theta.Real.gaussianVector_apply (since := "2026-11-23")]
alias gaussianVector_apply := Langlands.Theta.Real.gaussianVector_apply

@[deprecated Langlands.Theta.Real.gaussianVector_zero (since := "2026-11-23")]
alias gaussianVector_zero := Langlands.Theta.Real.gaussianVector_zero

@[deprecated Langlands.Theta.Real.isVacuumFor_one_gaussianVector (since := "2026-11-23")]
alias isVacuumFor_one_gaussianVector := Langlands.Theta.Real.isVacuumFor_one_gaussianVector

@[deprecated Langlands.Theta.Real.IsNormalizedLift (since := "2026-11-23")]
alias IsNormalizedLift := Langlands.Theta.Real.IsNormalizedLift

@[deprecated Langlands.Theta.Real.IsVacuumFor (since := "2026-11-23")]
alias IsVacuumFor := Langlands.Theta.Real.IsVacuumFor

@[deprecated Langlands.Theta.Real.IsVacuumFor.map (since := "2026-11-23")]
alias IsVacuumFor.map := Langlands.Theta.Real.IsVacuumFor.map

@[deprecated Langlands.Theta.Real.automorphyDet (since := "2026-11-23")]
alias automorphyDet := Langlands.Theta.Real.automorphyDet

@[deprecated Langlands.Theta.Real.automorphyLower (since := "2026-11-23")]
alias automorphyLower := Langlands.Theta.Real.automorphyLower

@[deprecated Langlands.Theta.Real.automorphyUpper (since := "2026-11-23")]
alias automorphyUpper := Langlands.Theta.Real.automorphyUpper

@[deprecated Langlands.Theta.Real.bigCellSection (since := "2026-11-23")]
alias bigCellSection := Langlands.Theta.Real.bigCellSection

@[deprecated Langlands.Theta.Real.det_automorphyUpper_ne_zero (since := "2026-11-23")]
alias det_automorphyUpper_ne_zero := Langlands.Theta.Real.det_automorphyUpper_ne_zero

@[deprecated Langlands.Theta.Real.holomorphicPart (since := "2026-11-23")]
alias holomorphicPart := Langlands.Theta.Real.holomorphicPart

@[deprecated Langlands.Theta.Real.isSiegel_siegelPoint (since := "2026-11-23")]
alias isSiegel_siegelPoint := Langlands.Theta.Real.isSiegel_siegelPoint

@[deprecated Langlands.Theta.Real.isSymm_siegelPoint (since := "2026-11-23")]
alias isSymm_siegelPoint := Langlands.Theta.Real.isSymm_siegelPoint

@[deprecated Langlands.Theta.Real.siegelPoint (since := "2026-11-23")]
alias siegelPoint := Langlands.Theta.Real.siegelPoint

@[deprecated Langlands.Theta.Real.Intertwines.exists_generator_mem_weylAlgebra (since := "2026-11-23")]
alias Intertwines.exists_generator_mem_weylAlgebra :=
  Langlands.Theta.Real.Intertwines.exists_generator_mem_weylAlgebra

@[deprecated Langlands.Theta.Real.exp_mem_symplecticGroup (since := "2026-11-23")]
alias exp_mem_symplecticGroup := Langlands.Theta.Real.exp_mem_symplecticGroup

@[deprecated Langlands.Theta.Real.mem_sp_of_exp_mem_symplecticGroup (since := "2026-11-23")]
alias mem_sp_of_exp_mem_symplecticGroup := Langlands.Theta.Real.mem_sp_of_exp_mem_symplecticGroup

@[deprecated Langlands.Theta.Real.automorphyDet_ne_zero (since := "2026-11-23")]
alias automorphyDet_ne_zero := Langlands.Theta.Real.automorphyDet_ne_zero

@[deprecated Langlands.Theta.Real.RealL2 (since := "2026-11-23"), reducible]
alias RealL2 := Langlands.Theta.Real.RealL2

@[deprecated Langlands.Theta.Real.RealSchwartz (since := "2026-11-23"), reducible]
alias RealSchwartz := Langlands.Theta.Real.RealSchwartz

@[deprecated Langlands.Theta.Real.circleSMul (since := "2026-11-23")]
alias circleSMul := Langlands.Theta.Real.circleSMul

@[deprecated Langlands.Theta.Real.circleSMul_apply (since := "2026-11-23")]
alias circleSMul_apply := Langlands.Theta.Real.circleSMul_apply

@[deprecated Langlands.Theta.Real.coeFn_schrodingerL2 (since := "2026-11-23")]
alias coeFn_schrodingerL2 := Langlands.Theta.Real.coeFn_schrodingerL2

@[deprecated Langlands.Theta.Real.coe_schrodingerSchwartz (since := "2026-11-23")]
alias coe_schrodingerSchwartz := Langlands.Theta.Real.coe_schrodingerSchwartz

@[deprecated Langlands.Theta.Real.continuous_fourierCharℂ (since := "2026-11-23")]
alias continuous_fourierCharℂ := Langlands.Theta.Real.continuous_fourierCharℂ

@[deprecated Langlands.Theta.Real.continuous_modulationPart (since := "2026-11-23")]
alias continuous_modulationPart := Langlands.Theta.Real.continuous_modulationPart

@[deprecated Langlands.Theta.Real.continuous_schrodingerL2 (since := "2026-11-23")]
alias continuous_schrodingerL2 := Langlands.Theta.Real.continuous_schrodingerL2

@[deprecated Langlands.Theta.Real.continuous_schrodingerL2_uncurry (since := "2026-11-23")]
alias continuous_schrodingerL2_uncurry := Langlands.Theta.Real.continuous_schrodingerL2_uncurry

@[deprecated Langlands.Theta.Real.continuous_translationPart (since := "2026-11-23")]
alias continuous_translationPart := Langlands.Theta.Real.continuous_translationPart

@[deprecated Langlands.Theta.Real.fourierCharℂ (since := "2026-11-23")]
alias fourierCharℂ := Langlands.Theta.Real.fourierCharℂ

@[deprecated Langlands.Theta.Real.fourierCharℂ_apply (since := "2026-11-23")]
alias fourierCharℂ_apply := Langlands.Theta.Real.fourierCharℂ_apply

@[deprecated Langlands.Theta.Real.hasTemperateGrowth_fourierCharℂ (since := "2026-11-23")]
alias hasTemperateGrowth_fourierCharℂ := Langlands.Theta.Real.hasTemperateGrowth_fourierCharℂ

@[deprecated Langlands.Theta.Real.modulationPart (since := "2026-11-23")]
alias modulationPart := Langlands.Theta.Real.modulationPart

@[deprecated Langlands.Theta.Real.modulationPart_add (since := "2026-11-23")]
alias modulationPart_add := Langlands.Theta.Real.modulationPart_add

@[deprecated Langlands.Theta.Real.modulationPart_apply (since := "2026-11-23")]
alias modulationPart_apply := Langlands.Theta.Real.modulationPart_apply

@[deprecated Langlands.Theta.Real.modulationPart_neg (since := "2026-11-23")]
alias modulationPart_neg := Langlands.Theta.Real.modulationPart_neg

@[deprecated Langlands.Theta.Real.modulationPart_smul (since := "2026-11-23")]
alias modulationPart_smul := Langlands.Theta.Real.modulationPart_smul

@[deprecated Langlands.Theta.Real.modulationPart_zero (since := "2026-11-23")]
alias modulationPart_zero := Langlands.Theta.Real.modulationPart_zero

@[deprecated Langlands.Theta.Real.norm_fourierCharℂ (since := "2026-11-23")]
alias norm_fourierCharℂ := Langlands.Theta.Real.norm_fourierCharℂ

@[deprecated Langlands.Theta.Real.schrodingerFun_real (since := "2026-11-23")]
alias schrodingerFun_real := Langlands.Theta.Real.schrodingerFun_real

@[deprecated Langlands.Theta.Real.schrodingerL2 (since := "2026-11-23")]
alias schrodingerL2 := Langlands.Theta.Real.schrodingerL2

@[deprecated Langlands.Theta.Real.schrodingerL2_comp (since := "2026-11-23")]
alias schrodingerL2_comp := Langlands.Theta.Real.schrodingerL2_comp

@[deprecated Langlands.Theta.Real.schrodingerL2_toLp (since := "2026-11-23")]
alias schrodingerL2_toLp := Langlands.Theta.Real.schrodingerL2_toLp

@[deprecated Langlands.Theta.Real.schrodingerL2_zero (since := "2026-11-23")]
alias schrodingerL2_zero := Langlands.Theta.Real.schrodingerL2_zero

@[deprecated Langlands.Theta.Real.schrodingerSchwartz (since := "2026-11-23")]
alias schrodingerSchwartz := Langlands.Theta.Real.schrodingerSchwartz

@[deprecated Langlands.Theta.Real.schrodingerUnitary (since := "2026-11-23")]
alias schrodingerUnitary := Langlands.Theta.Real.schrodingerUnitary

@[deprecated Langlands.Theta.Real.schrodingerUnitary_apply (since := "2026-11-23")]
alias schrodingerUnitary_apply := Langlands.Theta.Real.schrodingerUnitary_apply

@[deprecated Langlands.Theta.Real.translationPart (since := "2026-11-23")]
alias translationPart := Langlands.Theta.Real.translationPart

@[deprecated Langlands.Theta.Real.translationPart_add (since := "2026-11-23")]
alias translationPart_add := Langlands.Theta.Real.translationPart_add

@[deprecated Langlands.Theta.Real.translationPart_apply (since := "2026-11-23")]
alias translationPart_apply := Langlands.Theta.Real.translationPart_apply

@[deprecated Langlands.Theta.Real.translationPart_neg (since := "2026-11-23")]
alias translationPart_neg := Langlands.Theta.Real.translationPart_neg

@[deprecated Langlands.Theta.Real.translationPart_smul (since := "2026-11-23")]
alias translationPart_smul := Langlands.Theta.Real.translationPart_smul

@[deprecated Langlands.Theta.Real.translationPart_zero (since := "2026-11-23")]
alias translationPart_zero := Langlands.Theta.Real.translationPart_zero

@[deprecated Langlands.Theta.Real.oscillatorDeriv (since := "2026-11-23")]
alias oscillatorDeriv := Langlands.Theta.Real.oscillatorDeriv

@[deprecated Langlands.Theta.Real.oscillatorDeriv_commutator (since := "2026-11-23")]
alias oscillatorDeriv_commutator := Langlands.Theta.Real.oscillatorDeriv_commutator

@[deprecated Langlands.Theta.Real.oscillatorDeriv_fromBlocks_apply (since := "2026-11-23")]
alias oscillatorDeriv_fromBlocks_apply := Langlands.Theta.Real.oscillatorDeriv_fromBlocks_apply

@[deprecated Langlands.Theta.Real.schrodingerDeriv (since := "2026-11-23")]
alias schrodingerDeriv := Langlands.Theta.Real.schrodingerDeriv

@[deprecated Langlands.Theta.Real.schrodingerDeriv_add (since := "2026-11-23")]
alias schrodingerDeriv_add := Langlands.Theta.Real.schrodingerDeriv_add

@[deprecated Langlands.Theta.Real.schrodingerDeriv_apply (since := "2026-11-23")]
alias schrodingerDeriv_apply := Langlands.Theta.Real.schrodingerDeriv_apply

@[deprecated Langlands.Theta.Real.schrodingerDeriv_commutator (since := "2026-11-23")]
alias schrodingerDeriv_commutator := Langlands.Theta.Real.schrodingerDeriv_commutator

@[deprecated Langlands.Theta.Real.schrodingerDeriv_eq_sum (since := "2026-11-23")]
alias schrodingerDeriv_eq_sum := Langlands.Theta.Real.schrodingerDeriv_eq_sum

@[deprecated Langlands.Theta.Real.schrodingerDeriv_single_inl (since := "2026-11-23")]
alias schrodingerDeriv_single_inl := Langlands.Theta.Real.schrodingerDeriv_single_inl

@[deprecated Langlands.Theta.Real.schrodingerDeriv_single_inr (since := "2026-11-23")]
alias schrodingerDeriv_single_inr := Langlands.Theta.Real.schrodingerDeriv_single_inr

@[deprecated Langlands.Theta.Real.schrodingerDeriv_smul (since := "2026-11-23")]
alias schrodingerDeriv_smul := Langlands.Theta.Real.schrodingerDeriv_smul

@[deprecated Langlands.Theta.Real.exists_factor_through_toLp (since := "2026-11-23")]
alias exists_factor_through_toLp := Langlands.Theta.Real.exists_factor_through_toLp

@[deprecated Langlands.Theta.Real.exists_seminorm_le_sum_norm_toLp (since := "2026-11-23")]
alias exists_seminorm_le_sum_norm_toLp := Langlands.Theta.Real.exists_seminorm_le_sum_norm_toLp

@[deprecated Langlands.Theta.Real.fourierInv_schrodingerDeriv_inl (since := "2026-11-23")]
alias fourierInv_schrodingerDeriv_inl := Langlands.Theta.Real.fourierInv_schrodingerDeriv_inl

@[deprecated Langlands.Theta.Real.iteratedLineDerivOp_mem_weylAlgebra (since := "2026-11-23")]
alias iteratedLineDerivOp_mem_weylAlgebra :=
  Langlands.Theta.Real.iteratedLineDerivOp_mem_weylAlgebra

@[deprecated Langlands.Theta.Real.lineDerivOp_mem_weylAlgebra (since := "2026-11-23")]
alias lineDerivOp_mem_weylAlgebra := Langlands.Theta.Real.lineDerivOp_mem_weylAlgebra

@[deprecated Langlands.Theta.Real.schrodingerDeriv_mem_weylAlgebra (since := "2026-11-23")]
alias schrodingerDeriv_mem_weylAlgebra := Langlands.Theta.Real.schrodingerDeriv_mem_weylAlgebra

@[deprecated Langlands.Theta.Real.weylAlgebra (since := "2026-11-23")]
alias weylAlgebra := Langlands.Theta.Real.weylAlgebra

@[deprecated Langlands.Theta.Real.weylAlgebra.fourierInv_fourierWeight (since := "2026-11-23")]
alias weylAlgebra.fourierInv_fourierWeight :=
  Langlands.Theta.Real.weylAlgebra.fourierInv_fourierWeight

@[deprecated Langlands.Theta.Real.weylAlgebra.fourierInv_fourierWeight_pow (since := "2026-11-23")]
alias weylAlgebra.fourierInv_fourierWeight_pow :=
  Langlands.Theta.Real.weylAlgebra.fourierInv_fourierWeight_pow

@[deprecated Langlands.Theta.Real.weylAlgebra.fourierWeight (since := "2026-11-23")]
alias weylAlgebra.fourierWeight := Langlands.Theta.Real.weylAlgebra.fourierWeight

@[deprecated Langlands.Theta.Real.weylAlgebra.fourierWeight_mem (since := "2026-11-23")]
alias weylAlgebra.fourierWeight_mem := Langlands.Theta.Real.weylAlgebra.fourierWeight_mem

@[deprecated Langlands.Theta.Real.weylAlgebra.norm_weight_pow_apply (since := "2026-11-23")]
alias weylAlgebra.norm_weight_pow_apply := Langlands.Theta.Real.weylAlgebra.norm_weight_pow_apply

@[deprecated Langlands.Theta.Real.weylAlgebra.weight (since := "2026-11-23")]
alias weylAlgebra.weight := Langlands.Theta.Real.weylAlgebra.weight

@[deprecated Langlands.Theta.Real.weylAlgebra.weight_apply (since := "2026-11-23")]
alias weylAlgebra.weight_apply := Langlands.Theta.Real.weylAlgebra.weight_apply

@[deprecated Langlands.Theta.Real.weylAlgebra.weight_mem (since := "2026-11-23")]
alias weylAlgebra.weight_mem := Langlands.Theta.Real.weylAlgebra.weight_mem

@[deprecated Langlands.Theta.Real.weylAlgebra.weight_pow_apply (since := "2026-11-23")]
alias weylAlgebra.weight_pow_apply := Langlands.Theta.Real.weylAlgebra.weight_pow_apply

@[deprecated Langlands.Theta.Real.weylAlgebra_induction (since := "2026-11-23")]
alias weylAlgebra_induction := Langlands.Theta.Real.weylAlgebra_induction

@[deprecated Langlands.stdSymplecticForm (since := "2026-11-23")]
alias stdSymplecticForm := Langlands.stdSymplecticForm

@[deprecated Langlands.stdSymplecticForm_apply_eq_sum (since := "2026-11-23")]
alias stdSymplecticForm_apply_eq_sum := Langlands.stdSymplecticForm_apply_eq_sum

@[deprecated Langlands.stdSymplecticForm_apply (since := "2026-11-23")]
alias stdSymplecticForm_apply := Langlands.stdSymplecticForm_apply

@[deprecated Langlands.stdSymplecticForm_mulVec (since := "2026-11-23")]
alias stdSymplecticForm_mulVec := Langlands.stdSymplecticForm_mulVec

end Langlands.Theta
