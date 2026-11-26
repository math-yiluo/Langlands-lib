import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationStatement
import Langlands.Geometry.Manifold.EnvelopingAdjointOrbit
import Langlands.Global.InfiniteAdelicChartFormula
import Langlands.GroupScheme.RealWeilRegularFunctions
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Mathlib.Algebra.Group.Submonoid.Finite
import Mathlib.Data.Matrix.Basis

/-! # Conjugation fixes the center of the adelic enveloping algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped Classical CategoryTheory.MonObj ContDiff Manifold Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
open Langlands.Geometry.Manifold

private theorem linear_matrix_test {X K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]
    (S : Subalgebra ℝ (X → ℝ)) (m : X → Matrix n n K)
    (hm : ∀ (i j : n) (l : K →ₗ[ℝ] ℝ), (fun x => l (m x i j)) ∈ S)
    (l : Matrix n n K →ₗ[ℝ] ℝ) : (fun x => l (m x)) ∈ S := by
  have he : (fun x => l (m x)) = ∑ i, ∑ j,
      fun x => (l.comp (Matrix.singleLinearMap ℝ i j)) (m x i j) := by
    funext x
    simp only [Finset.sum_apply, LinearMap.comp_apply]
    conv_lhs => rw [Matrix.matrix_eq_sum_single (m x)]
    simp only [map_sum]
    rfl
  rw [he]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hm i j _

private theorem linear_conjugation_test {X A : Type*} [Group X] [Ring A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (S : Subalgebra ℝ (X → ℝ)) (r : X →* A)
    (hr : ∀ l : A →ₗ[ℝ] ℝ, (fun x => l (r x)) ∈ S)
    (hi : ∀ l : A →ₗ[ℝ] ℝ, (fun x => l (r (x⁻¹))) ∈ S)
    (Y : A) (l : A →ₗ[ℝ] ℝ) : (fun x => l (r x * Y * r (x⁻¹))) ∈ S := by
  let b := Module.finBasis ℝ A
  have hrep (X : A) : X = ∑ i, (b.coord i X) • b i := by
    simpa only [Module.Basis.coord_apply] using (b.sum_repr X).symm
  have he : (fun x => l (r x * Y * r (x⁻¹))) = ∑ i, ∑ j,
      ((fun x => b.coord i (r x)) * (fun x => b.coord j (r (x⁻¹)))) *
        algebraMap ℝ (X → ℝ) (l (b i * Y * b j)) := by
    funext x
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
    conv_lhs => rw [hrep (r x), hrep (r (x⁻¹))]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [he]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ =>
    S.mul_mem (S.mul_mem (hr _) (hi _)) (S.algebraMap_mem _)

/-- The adjoint action of every actual infinite adelic point is trivial on the center. -/
theorem adelicEnvelopingCenterConjugation : AdelicEnvelopingCenterConjugationStatement.{u} := by
  intro F _ _ G _ d hsmooth hG g z hz
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  let E := smoothModel F d
  let X := InfiniteAdelicGroupPoints F G
  let H (v : NumberField.InfinitePlace F) := InfinitePlaceGroupPoints.completionBaseChange F G v
  let Hp (v : NumberField.InfinitePlace F) := (H v).affinePoints (CommAlgCat.of v.Completion v.Completion)
  let Lp (v : NumberField.InfinitePlace F) := InfinitePlaceGroupPoints F G v
  let e := completions F G
  have hH (v : NumberField.InfinitePlace F) : IsConnectedReductive (H v) :=
    InfinitePlaceGroupPoints.isConnectedReductive_completionBaseChange F G hG v
  let (v : NumberField.InfinitePlace F) : IsAffine (H v).X.left := (hH v).affineScheme
  let (v : NumberField.InfinitePlace F) : TopologicalSpace (Hp v) :=
    (H v).affinePointsTopologicalSpace (CommAlgCat.of v.Completion v.Completion)
  let ev (v : NumberField.InfinitePlace F) : Lp v ≃ₜ* Hp v :=
    InfinitePlaceGroupPoints.completionBaseChangeHomeomorph F G v
  have hρ (v : NumberField.InfinitePlace F) : ∃ (n : ℕ) (ρ : MatrixRepresentation (H v) (Fin n)),
      IsClosedSubgroup ρ := by
    let : Smooth (H v).X.hom := (hH v).smooth
    exact affineLinearEmbeddingStatement v.Completion (H v) (hH v).isAffineHom inferInstance
  choose N ρ hρclosed using hρ
  let A := (v : NumberField.InfinitePlace F) → Matrix (Fin (N v)) (Fin (N v)) v.Completion
  let R (v : NumberField.InfinitePlace F) := InfinitePlaceGroupPoints.realizationMatrix F G v (ρ v)
  let r : X →* A := {
    toFun := fun x v => (R v (atPlace F G v x)).val
    map_one' := funext fun v => by
      change (R v (atPlace F G v 1)).val = 1
      simp
    map_mul' := fun x y => funext fun v => by
      change (R v (atPlace F G v (x * y))).val =
        (R v (atPlace F G v x)).val * (R v (atPlace F G v y)).val
      simp }
  have hentry (v : NumberField.InfinitePlace F) (i j : Fin (N v)) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, v.Completion) ∞ (fun x : X => r x v i j) :=
    (InfinitePlaceGroupPoints.contMDiff_iff_realizationMatrix F G v 𝓘(ℝ, E)
      hsmooth (ρ v) (hρclosed v) (atPlace F G v)).mp (contMDiff_atPlace F G hsmooth v) i j
  have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, A) ∞ (fun x : X => r x) := by
    apply contMDiff_pi_module_iff.mpr
    intro v
    let m : (Fin (N v) → Fin (N v) → v.Completion) →L[ℝ]
        Matrix (Fin (N v)) (Fin (N v)) v.Completion :=
      { toLinearMap := LinearMap.id, cont := continuous_id }
    exact m.contDiff.contMDiff.comp (contMDiff_pi_module_iff.mpr fun i =>
      contMDiff_pi_module_iff.mpr fun j => hentry v i j)
  let D := LinearAdjoint.tangent (E := E) r
  have hD : Function.Injective D := by
    apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective D.toLinearMap)
    rw [LinearMap.ker_eq_bot']
    intro Y hY
    apply eq_zero_of_zeroDeriv_realization F G hsmooth ρ hρclosed Y
    intro v i j
    let L : A →L[ℝ] v.Completion :=
      { toLinearMap := { toFun := fun a => a v i j, map_add' := fun _ _ => rfl,
                         map_smul' := fun _ _ => rfl }
        cont := (continuous_apply_apply i j).comp (continuous_apply v) }
    refine ⟨_, ((hentry v i j).mdifferentiableAt (by simp)).hasMFDerivAt, ?_⟩
    change mvfderiv 𝓘(ℝ, E) (fun x : X => L (r x)) 1 Y = 0
    rw [MatrixCoefficientLie.mvfderiv_clm_comp 𝓘(ℝ, E) (hr.mdifferentiableAt (by simp))]
    change L (D Y) = 0
    rw [show D Y = 0 from hY, map_zero]
  obtain ⟨p, hp⟩ := D.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hD)
  let P : A →L[ℝ] E := { p with cont := p.continuous_of_finiteDimensional }
  have hP (Y : GroupLieAlgebra 𝓘(ℝ, E) X) : P (D Y) = Y := DFunLike.congr_fun hp Y
  -- Pull back the algebra of real regular functions on each completion group.
  have hregular (v : NumberField.InfinitePlace F) := exists_realRegularFunctions v.Completion (H v) (hH v)
  choose Sv hSv hzero using hregular
  let ins (v : NumberField.InfinitePlace F) : Hp v →* X := e.symm.toMonoidHom.comp
    ((MonoidHom.mulSingle Lp v).comp (ev v).symm.toMonoidHom)
  have hIns (v : NumberField.InfinitePlace F) : Continuous (ins v) := e.symm.continuous.comp
    ((continuous_mulSingle v).comp (ev v).symm.continuous)
  let pull (v : NumberField.InfinitePlace F) : (X → ℝ) →ₐ[ℝ] (Hp v → ℝ) :=
    { toFun := fun f => f ∘ ins v, map_one' := rfl, map_zero' := rfl,
      map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  let S : Subalgebra ℝ (X → ℝ) := ⨅ v, (Sv v).comap (pull v)
  have memS (f : X → ℝ) : f ∈ S ↔ ∀ v, (fun x => f (ins v x)) ∈ Sv v :=
    Algebra.mem_iInf
  have hmatrix (v : NumberField.InfinitePlace F) (x : Hp v) : r (ins v x) =
      1 + LinearMap.single ℝ (fun w => Matrix (Fin (N w)) (Fin (N w)) w.Completion) v
        (((ρ v).affineMatrix (CommAlgCat.of v.Completion v.Completion) x).val - 1) := by
    funext w
    change (R w (atPlace F G w (ins v x))).val = 1 +
      (Pi.single (M := fun w => Matrix (Fin (N w)) (Fin (N w)) w.Completion) v
        (((ρ v).affineMatrix (CommAlgCat.of v.Completion v.Completion) x).val - 1)) w
    have he : atPlace F G w (ins v x) = Pi.mulSingle v ((ev v).symm x) w :=
      congrFun (e.apply_symm_apply (Pi.mulSingle v ((ev v).symm x))) w
    rw [he]
    by_cases hw : w = v
    · subst w
      rw [Pi.mulSingle_eq_same, Pi.single_eq_same]
      change ((ρ v).affineMatrix _ (ev v ((ev v).symm x))).val = _
      rw [ContinuousMulEquiv.apply_symm_apply]
      abel
    · rw [Pi.mulSingle_eq_of_ne hw, Pi.single_eq_of_ne hw, map_one, Units.val_one, add_zero]
  have hcoeff (v : NumberField.InfinitePlace F) (l : A →ₗ[ℝ] ℝ) :
      (fun x => l (r (ins v x))) ∈ Sv v ∧ (fun x => l (r ((ins v x)⁻¹))) ∈ Sv v := by
    let M : Hp v → GL (Fin (N v)) v.Completion := (ρ v).affineMatrix _
    let l' := l.comp (LinearMap.single ℝ (fun w => Matrix (Fin (N w)) (Fin (N w)) w.Completion) v)
    have hm : ∀ x : Hp v, l (r (ins v x)) = l 1 + l' (M x).val - l' 1 := by
      intro x
      rw [hmatrix, map_add]
      change l 1 + l' ((M x).val - 1) = _
      rw [map_sub, add_sub_assoc]
    have hfields (i j : Fin (N v)) (k : v.Completion →ₗ[ℝ] ℝ) :
        (fun x => k ((M x).val i j)) ∈ Sv v ∧ (fun x => k (((M x)⁻¹).val i j)) ∈ Sv v := by
      let B := CommAlgCat.of v.Completion v.Completion
      have he (x : Hp v) : (M x).val i j = (H v).affinePointEvaluation B x
          ((ρ v).hom.hom.left.appTop (GeneralLinear.entrySection (Fin (N v)) _ i j)) := by
        change GeneralLinear.affinePointsEquiv (Fin (N v)) (CommRingCat.of v.Completion) B
          (x ≫ (ρ v).hom.hom) i j = _
        rw [GeneralLinear.affinePointsEquiv_entry_evaluation, affinePointEvaluation_postcomp]
      have hi (x : Hp v) : ((M x)⁻¹).val i j = (H v).affinePointEvaluation B x
          ((ρ v).hom.hom.left.appTop (GeneralLinear.inverseEntrySection (Fin (N v)) _ i j)) := by
        change (GeneralLinear.affinePointsEquiv (Fin (N v)) (CommRingCat.of v.Completion) B
          (x ≫ (ρ v).hom.hom))⁻¹ i j = _
        rw [GeneralLinear.affinePointsEquiv_inverseEntry_evaluation, affinePointEvaluation_postcomp]
      exact ⟨by simp_rw [he]; exact hSv v _ k, by simp_rw [hi]; exact hSv v _ k⟩
    have hm₁ := linear_matrix_test (Sv v) (fun x => (M x).val)
      (fun i j k => (hfields i j k).1) l'
    have hm₂ := linear_matrix_test (Sv v) (fun x => ((M x)⁻¹).val)
      (fun i j k => (hfields i j k).2) l'
    have hc (a : ℝ) : (fun _ : Hp v => a) ∈ Sv v := (Sv v).algebraMap_mem a
    constructor
    · simp_rw [hm]
      exact (Sv v).sub_mem ((Sv v).add_mem (hc _) hm₁) (hc _)
    · simp_rw [← map_inv (ins v), hm, show ∀ x, M x⁻¹ = (M x)⁻¹ from fun x => map_inv ((ρ v).affineMatrix _) x]
      exact (Sv v).sub_mem ((Sv v).add_mem (hc _) hm₂) (hc _)
  have hreg (Y : GroupLieAlgebra 𝓘(ℝ, E) X) (l : E →ₗ[ℝ] ℝ) :
      (fun x => l (groupTangentConjugation 𝓘(ℝ, E) x Y)) ∈ S := by
    have heq : (fun x : X => l (groupTangentConjugation 𝓘(ℝ, E) x Y)) =
        fun x => (l.comp P.toLinearMap) (r x * D Y * r x⁻¹) :=
      funext fun x => congrArg l (LinearAdjoint.conjugation_eq r hr P hP Y x)
    rw [heq]
    exact linear_conjugation_test S r (fun l => (memS _).mpr fun v => (hcoeff v l).1)
      (fun l => (memS _).mpr fun v => (hcoeff v l).2) (D Y) (l.comp P.toLinearMap)
  let α := adelicEnvelopingConjugation F G hsmooth
  have ha₁ : α 1 = AlgHom.id ℂ (AdelicEnvelopingAlgebra F G hsmooth) :=
    adelicEnvelopingConjugation_one F G hsmooth
  have hamul (a b : X) : α (a * b) = (α a).comp (α b) :=
    adelicEnvelopingConjugation_mul F G hsmooth a b
  have hv (v : NumberField.InfinitePlace F) (x : Hp v) : α (ins v x) z = z := by
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℝ _).mp
    intro l
    have ⟨hm, hn⟩ := EnvelopingAdjoint.center_test S α
      ha₁ hamul
      (adelicEnvelopingConjugation_ι_tmul F G hsmooth)
      (LinearAdjoint.contMDiff_conjugation_apply r hr P hP)
      (LinearAdjoint.mfderiv_conjugation_apply r hr P hP) hreg z hz l
    let f := fun p : Hp v => l (α (ins v p) z) - l z
    have hf : f ∈ Sv v := (Sv v).sub_mem ((memS _).mp hm v) ((Sv v).algebraMap_mem _)
    have hnear : ∀ᶠ p in 𝓝 (1 : Hp v), f p = 0 := by
      have ht := (hIns v).continuousAt (x := (1 : Hp v)).tendsto
      rw [map_one] at ht
      filter_upwards [ht.eventually hn] with p hp
      exact sub_eq_zero.mpr hp
    simpa only [map_sub] using hzero v f hf hnear x
  let K : Submonoid ((v : NumberField.InfinitePlace F) → Lp v) := {
    carrier := {x | α (e.symm x) z = z}
    one_mem' := by
      change α (e.symm 1) z = z
      rw [map_one, ha₁, AlgHom.id_apply]
    mul_mem' := by
      intro x y hx hy
      change α (e.symm x) z = z at hx
      change α (e.symm y) z = z at hy
      change α (e.symm (x * y)) z = z
      rw [map_mul, hamul, AlgHom.comp_apply, hy, hx] }
  have hg : e g ∈ K := Submonoid.pi_mem_of_mulSingle_mem (e g) fun v => by
    have h := hv v (ev v (atPlace F G v g))
    change α (e.symm (Pi.mulSingle v ((ev v).symm (ev v (atPlace F G v g))))) z = z at h
    rw [ContinuousMulEquiv.symm_apply_apply] at h
    exact h
  change α (e.symm (e g)) z = z at hg
  simpa only [ContinuousMulEquiv.symm_apply_apply] using hg

end Langlands.Automorphic.GroupSchemeFunctions
