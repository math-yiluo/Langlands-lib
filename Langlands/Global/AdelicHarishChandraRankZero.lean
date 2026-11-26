import Langlands.Global.AdelicConvolutionApproximation
import Langlands.Global.AdelicConvolutionFiniteModel
import Langlands.Global.AdelicIntertwiningWeakContinuationReduction

/-! # Uniform convolution equations for rank-zero closed matrix representations -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local notation "X" => AdelicGroupPoints F G

omit [LocallyOfFiniteType G.X.hom] in
private theorem isInfiniteSubgroupFiniteFunction_of_subsingleton [Subsingleton X]
    (C : Subgroup (InfiniteAdelicGroupPoints F G)) (h : X → ℂ) :
    IsInfiniteSubgroupFiniteFunction F G C h := by
  have hconst : (fun (k : C) g => h (g * ofInfinite F G k.val)) = fun _ => h :=
    funext fun _ => funext fun _ => congrArg h (Subsingleton.elim _ _)
  unfold IsInfiniteSubgroupFiniteFunction
  rw [hconst, Set.range_const]
  infer_instance

/-- On a subsingleton adelic group, a single normalized kernel makes right convolution
the identity on every function. -/
theorem hasConvolutionEquationAt_of_subsingleton_points [Subsingleton X] {d n : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (C : Subgroup (InfiniteAdelicGroupPoints F G))
    (f : (Fin n → ℂ) → X → ℂ) (s₀ : Fin n → ℂ) :
    HasConvolutionEquationAt C f s₀ := by
  obtain ⟨k, hk, -, -, hmass⟩ :=
    exists_normalizedAdelicTestFunction hsmooth (Filter.univ_mem : Set.univ ∈ 𝓝 (1 : X))
  let h (x : X) : ℂ := k x
  refine ⟨1, fun _ => h, fun _ _ => 1, fun _ => 1, fun _ => ⟨hk,
      isInfiniteSubgroupFiniteFunction_of_subsingleton C h,
      isInfiniteSubgroupFiniteFunction_of_subsingleton C (fun x => h x⁻¹)⟩,
    fun _ => differentiable_const _, differentiable_const _, one_ne_zero, fun s x => ?_⟩
  simp only [Fin.sum_univ_one, one_mul, rightConvolution]
  have htranslate (t : X) : f s (x * t) = f s x :=
    congrArg (f s) (Subsingleton.elim _ _)
  simp_rw [htranslate, integral_mul_const]
  rw [show (∫ t, h t ∂(Measure.haar : Measure X)) = 1 by
    rw [show h = (fun t => ((k t : ℝ) : ℂ)) from rfl, integral_complex_ofReal, hmass,
      Complex.ofReal_one], one_mul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme

/-- A closed embedding into `GL₀` places no restriction on the parameterized function
family for the uniform convolution equation. -/
def HarishChandraRankZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (rho : MatrixRepresentation G (Fin 0)), IsClosedSubgroup rho →
    ∀ {d n : ℕ}, SmoothOfRelativeDimension d G.X.hom → ∀ (C : Subgroup (InfiniteAdelicGroupPoints F G))
      (f : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ) (s₀ : Fin n → ℂ),
      HasConvolutionEquationAt C f s₀

theorem harishChandraRankZero : HarishChandraRankZeroStatement.{u} := by
  intro F _ _ G _ _ rho hrho d n hsmooth C f s₀
  let := subsingleton_adelicGroupPoints_of_rank_zero' rho hrho
  exact hasConvolutionEquationAt_of_subsingleton_points hsmooth C f s₀

end Langlands.Global
