import Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The unramified complex exponential is a local biholomorphism -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.Plancherel

private theorem isLocalDiffeomorph_scaledExp (r : ℕ) (c : ℂ) (hc : c ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ) ω
      (fun (s : Fin r → ℂ) i => Complex.exp (c * s i)) := by
  let E := Fin r → ℂ
  let expCoords : E → E := fun s i => Complex.exp (c * s i)
  have hanalytic : ContDiff ℂ ω expCoords := by
    apply contDiff_pi.mpr
    intro i
    exact Complex.contDiff_exp.comp (contDiff_const.mul (contDiff_apply ℂ ℂ i))
  let derivative (s : E) : E ≃L[ℂ] E :=
    ContinuousLinearEquiv.piCongrRight fun i =>
      ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0 (Complex.exp (c * s i) * c) (mul_ne_zero (Complex.exp_ne_zero _) hc))
  have hderivative (s : E) : HasFDerivAt expCoords (derivative s : E →L[ℂ] E) s := by
    apply hasFDerivAt_pi'.2
    intro i
    have hi : HasDerivAt (fun z : ℂ => Complex.exp (c * z))
        (Complex.exp (c * s i) * c) (s i) := by
      simpa only [mul_one] using ((hasDerivAt_id' (s i)).const_mul c).cexp
    have hp : HasFDerivAt (fun x : E => x i) (ContinuousLinearMap.proj (R := ℂ) i) s :=
      hasFDerivAt_apply i s
    have h := (hi.hasFDerivAt_equiv (mul_ne_zero (Complex.exp_ne_zero _) hc)).comp s hp
    exact h
  intro s
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let e := hanalytic.contDiffAt.toOpenPartialHomeomorph expCoords (hderivative s) hω
  refine ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hanalytic.contMDiff.contMDiffOn
    contMDiffOn_invFun := ?_ }, ?_, fun _ _ => rfl⟩
  · change ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω e.symm e.target
    rw [contMDiffOn_iff_contDiffOn]
    intro z hz
    exact (e.contDiffAt_symm hz (hderivative (e.symm z)) hanalytic.contDiffAt).contDiffWithinAt
  · exact hanalytic.contDiffAt.mem_toOpenPartialHomeomorph_source (hderivative s) hω

/-- In the coordinates of any integer basis of the valuation image, the canonical
unramified complex exponential is a local biholomorphism (Renard V.3.20). -/
theorem rationalUnramifiedComplexExponential :
    RationalUnramifiedComplexExponentialStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro b
  let := rationalUnramifiedBasisChartedSpace G b
  let E := Fin (rationalImageRank G) → ℂ
  let X := unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)
  let f : E → X := fun s => rationalCanonicalUnramifiedComplexExponential G
    (Multiplicative.ofAdd (b.constr ℤ s).toAddMonoidHom)
  let c : ℂ := -(Real.log (LocalField.residueCardinality F : ℝ) : ℂ)
  have hlog : 0 < Real.log (LocalField.residueCardinality F : ℝ) :=
    Real.log_pos (by exact_mod_cast LocalField.residueCardinality_gt_one F)
  have hc : c ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hlog.ne')
  have hcoords : rationalUnramifiedBasisCoordinates G b ∘ f =
      fun s i => Complex.exp (c * s i) := by
    funext s i
    obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (b i).toMul
    change rationalUnramifiedBasisCoordinates G b (f s) i = _
    rw [rationalUnramifiedBasisCoordinates_apply G b (f s) i g hg]
    dsimp only [f]
    rw [rationalCanonicalUnramifiedComplexExponential_val, hg]
    change Complex.exp (-(b.constr ℤ s (b i)) * _) = _
    rw [Module.Basis.constr_basis]
    simp only [c, neg_mul, mul_comm (s i)]
  have hlocal : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) ω
      (rationalUnramifiedBasisCoordinates G b ∘ f) := by
    rw [hcoords]
    exact isLocalDiffeomorph_scaledExp _ c hc
  have hchart := isOpenEmbedding_rationalUnramifiedBasisCoordinates G b
  let chart := hchart.toOpenPartialHomeomorph (rationalUnramifiedBasisCoordinates G b)
  let chartDiffeomorph : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) X E ω := {
    toPartialEquiv := chart.toPartialEquiv
    open_source := chart.open_source
    open_target := chart.open_target
    contMDiffOn_toFun := (contMDiff_isOpenEmbedding (I := 𝓘(ℂ, E)) (n := ω) hchart).contMDiffOn
    contMDiffOn_invFun := by
      change ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω chart.symm chart.target
      rw [hchart.toOpenPartialHomeomorph_target]
      exact contMDiffOn_isOpenEmbedding_symm hchart }
  intro s
  change IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω f s
  have hs : (rationalUnramifiedBasisCoordinates G b ∘ f) s ∈ chartDiffeomorph.symm.source := by
    change _ ∈ chart.target
    rw [hchart.toOpenPartialHomeomorph_target]
    exact ⟨f s, rfl⟩
  have hcancel : chartDiffeomorph.symm ∘ (rationalUnramifiedBasisCoordinates G b ∘ f) = f :=
    funext fun _ => hchart.toOpenPartialHomeomorph_left_inv _
  rw [← hcancel]
  exact IsLocalDiffeomorphAt.comp 𝓘(ℂ, E) X (hlocal s)
    (chartDiffeomorph.symm.isLocalDiffeomorphAt _ _ _ hs)

end Langlands.Plancherel
