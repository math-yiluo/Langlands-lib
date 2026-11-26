import Langlands.Global.AdelicTwistedConvolution
import Langlands.Global.AdelicEisensteinConvolutionIdentity
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.EisensteinEvaluationMatrix
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Analysis.SeveralComplex.ParametricIntegral

/-! # Entire coefficients of a finite-dimensional adelic induced convolution family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Analysis.Meromorphic Langlands.Analysis.SeveralComplex

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The integrated induced action is pointwise entire for continuous input and a continuous,
compactly supported kernel. -/
theorem IsIwasawaCompact.isHolomorphicInCoordinatesOn_inducedConvolution
    (hK : IsIwasawaCompact p K) [FiniteDimensional ℂ (ComplexCharacterParameter F P)]
    {φ v : AdelicGroupPoints F G → ℂ} (hφ : Continuous φ) (hsupp : HasCompactSupport φ)
    (hv : Continuous v) (g : AdelicGroupPoints F G) :
    IsHolomorphicInCoordinatesOn (fun lam => hK.inducedConvolution lam φ v g) Set.univ := by
  refine ⟨inferInstance, fun n e => ?_⟩
  rw [Set.preimage_univ]
  apply isHolomorphicOn_of_differentiableOn
  let haar : Measure (AdelicGroupPoints F G) := Measure.haar
  let restricted := haar.restrict (tsupport φ)
  let : IsFiniteMeasure restricted := ⟨by simpa [restricted, Measure.restrict_apply_univ] using
    (hsupp.measure_lt_top : haar (tsupport φ) < ⊤)⟩
  let integrand (s : Fin n → ℂ) (h : AdelicGroupPoints F G) : ℂ :=
    φ h * hK.inducedRightTranslate (e s) h v g
  have hdiff (h : AdelicGroupPoints F G) : Differentiable ℂ fun s => integrand s h := by
    exact (differentiable_const _).mul
      ((hK.differentiable_heightPower (-e.toLinearMap) g).mul
        ((differentiable_const _).mul (hK.differentiable_heightPower e.toLinearMap (g * h))))
  have hcont : Continuous (fun z : (Fin n → ℂ) × AdelicGroupPoints F G => integrand z.1 z.2) := by
    have hleft : Continuous fun z : (Fin n → ℂ) × AdelicGroupPoints F G =>
        hK.heightPower (-(e z.1)) g :=
      (hK.differentiable_heightPower (-e.toLinearMap) g).continuous.comp continuous_fst
    have hg : Continuous fun z : (Fin n → ℂ) × AdelicGroupPoints F G => g * z.2 :=
      continuous_const.mul continuous_snd
    have hright : Continuous fun z : (Fin n → ℂ) × AdelicGroupPoints F G =>
        hK.heightPower (e z.1) (g * z.2) :=
      Complex.continuous_exp.comp ((continuous_complexParameterPairing_coordinates e.toLinearMap
        ).comp (continuous_fst.prodMk (hK.continuous_height.comp hg)))
    exact (hφ.comp continuous_snd).mul (hleft.mul ((hv.comp hg).mul hright))
  have hzero (s : Fin n → ℂ) {h : AdelicGroupPoints F G} (hh : h ∉ tsupport φ) :
      integrand s h = 0 := by
    simp [integrand, image_eq_zero_of_notMem_tsupport hh]
  have hmeas (s : Fin n → ℂ) : AEStronglyMeasurable (integrand s) restricted :=
    (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound (C : Set (Fin n → ℂ)) (hC : IsCompact C) :
      ∃ B : ℝ, ∀ s ∈ C, ∀ h, ‖integrand s h‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hC.prod hsupp).bddAbove_image hcont.norm.continuousOn
    refine ⟨max B 0, fun s hs h => ?_⟩
    by_cases hh : h ∈ tsupport φ
    · exact (hB ⟨(s, h), ⟨hs, hh⟩, rfl⟩).trans (le_max_left _ _)
    · rw [hzero s hh, norm_zero]
      exact le_max_right _ _
  have hd := differentiableOn_integral_of_bounded restricted integrand isOpen_univ
    (fun h => (hdiff h).differentiableOn) (fun s _ => hmeas s) (fun C _ => hbound C)
  refine hd.congr fun s _ => ?_
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero («μ» := haar) (fun _ => hzero s)).symm

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic

/-- Once the values of an induced convolution family span a finite-dimensional space, its
expansion in a basis selected from that family has entire coefficients. -/
def InducedConvolutionEntireCoefficientsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact p K) [FiniteDimensional ℂ (ComplexCharacterParameter F P)]
    (φ v : AdelicGroupPoints F G → ℂ), Continuous φ → HasCompactSupport φ → Continuous v →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun lam => hK.inducedConvolution lam φ v))) →
    ∃ (m : ℕ) (w : Fin m → AdelicGroupPoints F G → ℂ)
      (b : Fin m → ComplexCharacterParameter F P → ℂ),
      (∀ i, ∃ lam, hK.inducedConvolution lam φ v = w i) ∧
      (∀ i, IsHolomorphicInCoordinatesOn (b i) Set.univ) ∧
      ∀ lam, hK.inducedConvolution lam φ v = fun x => ∑ i, b i lam * w i x

/-- Extract the coordinates of the operator by finitely many point evaluations. -/
theorem inducedConvolutionEntireCoefficients : InducedConvolutionEntireCoefficientsStatement.{u} := by
  intro F _ _ G P _ _ _ p _ K hK _ φ v hφ hsupp hv hfinite
  classical
  let f := fun lam => hK.inducedConvolution lam φ v
  let W := Submodule.span ℂ (Set.range f)
  let lift (lam : ComplexCharacterParameter F P) : W := ⟨f lam, Submodule.subset_span ⟨lam, rfl⟩⟩
  let : FiniteDimensional ℂ W := hfinite
  obtain ⟨w, hw, hspan, hind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range f)
  let wBasis := Module.Basis.span hind
  let transfer := LinearEquiv.ofEq _ _ hspan
  let coords := transfer.symm.trans wBasis.equivFun
  obtain ⟨points, ev, heval⟩ := EisensteinJet.exists_evaluationEquiv W.subtype Subtype.val_injective
  refine ⟨_, w, fun i lam => coords (lift lam) i, hw, fun i => ?_, fun lam => ?_⟩
  · refine ⟨inferInstance, fun n e => ?_⟩
    let lin : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] ℂ :=
      (LinearMap.proj i).comp (coords.toLinearMap.comp ev.symm.toLinearMap)
    have heq : (fun s : Fin n → ℂ => coords (lift (e s)) i) =
        fun s => lin (fun j => f (e s) (points j)) := by
      funext s
      have hp : (fun j => f (e s) (points j)) = ev (lift (e s)) := funext fun j =>
        (heval (lift (e s)) j).symm
      rw [hp]
      simp [lin]
    rw [Set.preimage_univ]
    apply isHolomorphicOn_of_differentiableOn
    change DifferentiableOn ℂ (fun s : Fin n → ℂ => coords (lift (e s)) i) Set.univ
    rw [heq]
    apply lin.toContinuousLinearMap.differentiable.comp_differentiableOn
    apply differentiableOn_pi.mpr
    intro j
    have hhol := (hK.isHolomorphicInCoordinatesOn_inducedConvolution hφ hsupp hv (points j)).2 n e
    rw [Set.preimage_univ] at hhol
    exact differentiableOn_of_isHolomorphicOn hhol
  · funext x
    have heq := congrArg (fun z : Submodule.span ℂ (Set.range w) => z.val x)
      (wBasis.sum_equivFun (transfer.symm (lift lam)))
    simpa [wBasis, coords, transfer, lift, f, smul_eq_mul, Finset.sum_apply] using heq.symm

end Langlands.Global
