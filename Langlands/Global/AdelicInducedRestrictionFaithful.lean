import Langlands.Global.AdelicInducedInnerProductGramProof
import Langlands.Global.AdelicInducedL2Inner
import Langlands.Global.AdelicSquareIntegrableInducedSubmodule

/-! # Faithfulness of restriction for square-integrable inducing forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : Measure (AdelicGroupPoints F M)} [μM.IsHaarMeasure] {n : ℕ}
  {e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P} {β : (Fin n → ℝ) → ℝ}

/-- Two `A²_P` functions that agree almost everywhere on the weighted Iwasawa restriction
are equal as functions on `G(𝔸)`. -/
theorem eq_of_ae_inducedRestriction
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l iU))
    (hβc : Continuous β) (hβs : HasCompactSupport β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβint : ∫ x, β x = 1) {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ)
    (hψ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l ψ)
    (h : inducedRestriction K p l φ =ᵐ[inducedL2Measure K hK.isCompact l μM e β]
      inducedRestriction K p l ψ) : φ = ψ := by
  let m := inducedL2Measure K hK.isCompact l μM e β
  have hdiff : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (φ - ψ) :=
    (squareIntegrableInducedForms p l hK.isCompact rho hsmooth hcalc iU).sub_mem hφ hψ
  have hf : (0 : Lp ℂ 2 m) =ᵐ[m] inducedRestriction K p l (φ - ψ) := by
    filter_upwards [Lp.coeFn_zero ℂ 2 m, h] with x hz heq
    rw [hz]
    exact (sub_eq_zero.mpr heq).symm
  have hdiag := inner_eq_inducedInnerProduct K hK.isCompact p l μM e β hβc hβ0
    (0 : Lp ℂ 2 m) 0 (φ - ψ) (φ - ψ) hf hf
  rw [inner_zero_left] at hdiag
  have hgram := (inducedInnerProductGram F G P M U p iU l hG hp hU hl hmul K hK rho hsmooth
    hcalc μM e β hβc hβs hβint 1 (fun _ => φ - ψ) (fun _ => hdiff) (fun _ => 1)).2
  apply sub_eq_zero.mp
  simpa only [Fin.sum_univ_one, map_one, one_mul, one_smul] using hgram.mp (by simpa using hdiag.symm)

end Langlands.Global.AdelicGroupPoints
