import Langlands.Automorphic.GeneralLinearAutomorphicTaylorMap
import Langlands.Automorphic.OperatorCompactCompatibility

/-! # Continuous scalar tests for the actual matrix automorphic operators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearOperatorEvaluationAffine :
    IsAffine (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearOperatorEvaluationAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GL[F, n]) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "Ambient" => Langlands.Automorphic.FiniteSmoothRationalFunctions F n
local notation "Enveloping" => ArchimedeanGL.EnvelopingAlgebra F n
local notation "D" => finiteSmoothEnvelopingAction F n

private def matrixEvaluation (x : AdelicGL F n) : Ambient →ₗ[ℂ] ℂ where
  toFun f := ContinuousRationalFunctions.evaluate F n f.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def derivativeTest (b : Enveloping) (x : AdelicGL F n) : Ambient →ₗ[ℂ] ℂ :=
  (matrixEvaluation F n x).comp (D b)

private abbrev derivativeTests : Set (Ambient →ₗ[ℂ] ℂ) :=
  Set.range fun p : Enveloping × AdelicGL F n => derivativeTest F n p.1 p.2

private theorem derivativeTest_comp_finite (b : Enveloping) (x : AdelicGL F n)
    (g : FiniteAdelicGL F n) :
    (derivativeTest F n b x).comp (finiteSmoothFiniteRightAction F n g) =
      derivativeTest F n b (x * AdelicGL.ofFinite F n g) := by
  ext f
  change matrixEvaluation F n x (D b (finiteSmoothFiniteRightAction F n g f)) = _
  rw [← finiteSmoothFiniteRightAction_envelopingAction]
  rfl

private theorem derivativeTest_comp_compact (b : Enveloping) (x : AdelicGL F n)
    (k : standardInfiniteCompact F n) :
    (derivativeTest F n b x).comp (finiteSmoothCompactRightAction F n k) =
      derivativeTest F n (ArchimedeanGL.envelopingConjugation F n k.val⁻¹ b)
        (x * AdelicGL.ofInfinite F n k.val) := by
  ext f
  have h := finiteSmoothRightAction_envelopingAction k.val
    (ArchimedeanGL.envelopingConjugation F n k.val⁻¹ b) f
  rw [ArchimedeanGL.envelopingConjugation_inv, AlgEquiv.apply_symm_apply] at h
  change matrixEvaluation F n x
    (D b (Langlands.Automorphic.finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) f)) = _
  rw [← h]
  rfl

private theorem derivativeTest_comp_differential (b c : Enveloping) (x : AdelicGL F n) :
    (derivativeTest F n b x).comp (D c) = derivativeTest F n (b * c) x := by
  ext f
  change matrixEvaluation F n x (D b (D c f)) = matrixEvaluation F n x (D (b * c) f)
  rw [map_mul, Module.End.mul_apply]

private theorem derivativeSpan_preserved (a : automorphicOperatorAlgebra F n) :
    ∀ l ∈ Submodule.span ℂ (derivativeTests F n),
      l.comp a.val ∈ Submodule.span ℂ (derivativeTests F n) := by
  let S := Submodule.span ℂ (derivativeTests F n)
  change ∀ l ∈ S, l.comp a.val ∈ S
  refine Algebra.adjoin_induction (p := fun a _ => ∀ l ∈ S, l.comp a ∈ S)
    ?_ ?_ ?_ ?_ a.property
  · intro a ha l hl
    let pullback := LinearMap.lcomp ℂ ℂ a
    have hle : S ≤ S.comap pullback := Submodule.span_le.mpr (by
      rintro _ ⟨⟨b, x⟩, rfl⟩
      change (derivativeTest F n b x).comp a ∈ S
      rcases ha with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨c, rfl⟩
      · rw [derivativeTest_comp_finite]
        exact Submodule.subset_span ⟨(b, x * AdelicGL.ofFinite F n g), rfl⟩
      · rw [derivativeTest_comp_compact]
        exact Submodule.subset_span ⟨(_, _), rfl⟩
      · rw [derivativeTest_comp_differential]
        exact Submodule.subset_span ⟨(b * c, x), rfl⟩)
    exact hle hl
  · intro c l hl
    have h : l.comp (algebraMap ℂ (FiniteSmoothEnd F n) c) = c • l := by
      ext f
      change l (c • f) = c • l f
      exact map_smul l c f
    rw [h]
    exact S.smul_mem c hl
  · intro a b _ _ ha hb l hl
    rw [LinearMap.comp_add]
    exact S.add_mem (ha l hl) (hb l hl)
  · intro a b _ _ ha hb l hl
    change (l.comp a).comp b ∈ S
    exact hb _ (ha l hl)

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))

local notation "V" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "Adeles" => AdelicGroupPoints F GL[F, n]

private abbrev matrixFunction (v : V) : Ambient :=
  finitePlotSmoothGeneralLinearEquiv F n
    (v : uniformGrowthLevelSubmodule F GL[F, n] rho hsmooth hcalc R L).val

private theorem exists_continuous_test (l : Ambient →ₗ[ℂ] ℂ)
    (hl : l ∈ Submodule.span ℂ (derivativeTests F n)) :
    ∃ t : V →L[ℂ] ℂ, ∀ f, t f = l (matrixFunction F n rho hsmooth hcalc hN hrho R L f) := by
  induction hl using Submodule.span_induction with
  | mem l hl =>
    obtain ⟨⟨b, x⟩, rfl⟩ := hl
    let e := GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc
    obtain ⟨c, rfl⟩ := e.surjective b
    obtain ⟨y, rfl⟩ := (GeneralLinearGroupPoints.adelicHomeomorph F n).surjective x
    refine ⟨differentialEvaluation F GL[F, n] rho hsmooth hcalc hN hrho R L c y, fun f => ?_⟩
    rw [differentialEvaluation_apply]
    let g : FinitePlotSmoothRationalFunctions F GL[F, n] :=
      (f : uniformGrowthLevelSubmodule F GL[F, n] rho hsmooth hcalc R L).val
    change evaluate F GL[F, n] (adelicEnvelopingAction F GL[F, n] hsmooth hcalc c g).val y =
      matrixEvaluation F n (GeneralLinearGroupPoints.adelicHomeomorph F n y)
        (D (e c) (finitePlotSmoothGeneralLinearEquiv F n g))
    rw [← finitePlotSmoothGeneralLinearEquiv_envelopingAction F n hsmooth hcalc c g]
    exact (evaluate_continuousGeneralLinearEquiv_at_point F n _ y).symm
  | zero => exact ⟨0, fun _ => rfl⟩
  | add l m _ _ hl hm =>
    obtain ⟨tl, htl⟩ := hl
    obtain ⟨tm, htm⟩ := hm
    exact ⟨tl + tm, fun f => by simp only [add_apply, htl, htm, LinearMap.add_apply]⟩
  | smul a l _ hl =>
    obtain ⟨tl, htl⟩ := hl
    exact ⟨a • tl, fun f => by simp only [smul_apply, htl, LinearMap.smul_apply]⟩

private theorem matrixEvaluation_mem_span (x : AdelicGL F n) :
    matrixEvaluation F n x ∈ Submodule.span ℂ (derivativeTests F n) := by
  have h : derivativeTest F n 1 x = matrixEvaluation F n x := by
    rw [derivativeTest, map_one, Module.End.one_eq_id, LinearMap.comp_id]
  rw [← h]
  exact Submodule.subset_span ⟨(1, x), rfl⟩

/-- Evaluation after an arbitrary concrete automorphic operator is continuous
on the original fixed-level growth space. -/
theorem exists_generalLinearOperatorEvaluation (a : automorphicOperatorAlgebra F n) (x : Adeles) :
    ∃ test : V →L[ℂ] ℂ, ∀ f, test f = ContinuousRationalFunctions.evaluate F n
      (a.val (matrixFunction F n rho hsmooth hcalc hN hrho R L f)).val
      (GeneralLinearGroupPoints.adelicHomeomorph F n x) := by
  let p := GeneralLinearGroupPoints.adelicHomeomorph F n x
  exact exists_continuous_test F n rho hsmooth hcalc hN hrho R L _
    (derivativeSpan_preserved F n a _ (matrixEvaluation_mem_span F n p))

/-- The continuous scalar test realizing evaluation after a concrete operator. -/
def generalLinearOperatorEvaluation (a : automorphicOperatorAlgebra F n) (x : Adeles) : V →L[ℂ] ℂ :=
  (exists_generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L a x).choose

@[simp]
theorem generalLinearOperatorEvaluation_apply (a : automorphicOperatorAlgebra F n)
    (x : Adeles) (f : V) :
    generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L a x f =
      ContinuousRationalFunctions.evaluate F n
        (a.val (matrixFunction F n rho hsmooth hcalc hN hrho R L f)).val
        (GeneralLinearGroupPoints.adelicHomeomorph F n x) :=
  (exists_generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L a x).choose_spec f

/-- Scalar Taylor evaluation commutes with every concrete operator on the stable module. -/
theorem evaluate_operator_stableGeneralLinearTaylorCoefficient
    (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, n])
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n]))) {U O : Set ℂ}
    (hU : IsPreconnected U) (hUo : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U) (hne : O.Nonempty)
    (f : ℂ → V) (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hform : ∀ t ∈ O, IsAutomorphicFunctionOn F GL[F, n] hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F GL[F, n]) (generalLinearStandardInfiniteCompact F n)
      rho (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f t)))
    (z : U) (k : ℕ) (a : automorphicOperatorAlgebra F n) (x : Adeles) :
    stableGeneralLinearEvaluation F n (stableAutomorphicAction F n a
      (stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
        hU hUo hO hOU hne f hf hform z k)) x =
      iteratedDeriv k (fun t => generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L a x
        (f t)) z.val / (k.factorial : ℂ) := by
  let c := taylorCoefficient F GL[F, n] rho hsmooth hcalc hN hrho R L hL hUo f hf k z
  let C := stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
    hU hUo hO hOU hne f hf hform z k
  have hC : C.val = matrixFunction F n rho hsmooth hcalc hN hrho R L c := by
    simp only [C, stableGeneralLinearTaylorCoefficient, stableAutomorphicEquiv_symm_val,
      adelicAutomorphicGeneralLinearMap_val]
    rfl
  change ContinuousRationalFunctions.evaluate F n (a.val C.val).val
    (GeneralLinearGroupPoints.adelicHomeomorph F n x) = _
  rw [hC, ← generalLinearOperatorEvaluation_apply]
  exact apply_taylorCoefficient F GL[F, n] rho hsmooth hcalc hN hrho R L hL hUo f hf k z
    (generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L a x)

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
