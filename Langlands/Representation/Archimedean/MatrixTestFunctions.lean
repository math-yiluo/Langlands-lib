import Langlands.Analysis.SmoothTestFunctionOperations
import Langlands.Representation.Archimedean.GardingFunctionals
import Langlands.Representation.Archimedean.PrincipalSeriesStability

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff Distributions Matrix.Norms.Operator

namespace Langlands.Archimedean

universe uF

variable {F : Type uF} [RCLike F] {n : ℕ}

/-- The open subset of invertible matrices in the real matrix model of `GL_n(F)`. -/
def matrixUnitsOpen (F : Type uF) [RCLike F] (n : ℕ) :
    Opens (Matrix (Fin n) (Fin n) F) :=
  ⟨{x | IsUnit x}, isOpen_setOf_isUnit_matrix⟩

private theorem tsupport_unitsExtension_subset {f : Langlands.GeneralLinear n F → ℂ}
    (hf : HasCompactSupport f) :
    tsupport (unitsExtension f) ⊆ (Units.val : Langlands.GeneralLinear n F → _) '' tsupport f := by
  apply closure_minimal _ (hf.image Units.continuous_val).isClosed
  intro x hx
  by_cases h : IsUnit x
  · obtain ⟨g, rfl⟩ := h
    refine ⟨g, subset_tsupport f ?_, rfl⟩
    simpa only [mem_support, unitsExtension_val] using hx
  · exact (hx (unitsExtension_of_not_isUnit f h)).elim

private theorem contDiff_unitsExtension_of_hasCompactSupport
    {f : Langlands.GeneralLinear n F → ℂ}
    (hf : ContMDiff (matrixModel F n) 𝓘(ℝ, ℂ) ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (unitsExtension f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : IsUnit x
  · exact (contDiffOn_unitsExtension hf).contDiffAt (isOpen_setOf_isUnit_matrix.mem_nhds hx)
  · have hnot : x ∉ tsupport (unitsExtension f) := fun hs => by
      obtain ⟨g, _, rfl⟩ := tsupport_unitsExtension_subset hc hs
      exact hx (Units.isUnit g)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnot] with y hy
    by_contra h
    exact hy (subset_tsupport _ h)

private theorem hasCompactSupport_restrict_matrixTestFunction
    (f : 𝓓(matrixUnitsOpen F n, ℂ)) :
    HasCompactSupport (f ∘ (Units.val : Langlands.GeneralLinear n F → _)) := by
  have hr : tsupport f ⊆ Set.range (Units.val : Langlands.GeneralLinear n F → _) := by
    rw [range_val_eq_setOf_isUnit]
    exact f.tsupport_subset
  have he : Topology.IsOpenEmbedding (Units.val : Langlands.GeneralLinear n F → _) :=
    Units.isOpenEmbedding_val
  exact (he.isEmbedding.isInducing.isCompact_preimage' f.hasCompactSupport hr).of_isClosed_subset
    isClosed_closure (tsupport_comp_subset_preimage _ he.continuous)

/-- Restriction to the units, with inverse given by extension by zero. -/
def matrixTestFunctionKernelEquiv :
    𝓓(matrixUnitsOpen F n, ℂ) ≃ₗ[ℂ]
      smoothCompactKernels (Matrix (Fin n) (Fin n) F) (Langlands.GeneralLinear n F) where
  toFun f :=
    ⟨f ∘ Units.val, f.contDiff.contMDiff.comp Units.contMDiff_val,
      hasCompactSupport_restrict_matrixTestFunction f⟩
  invFun f := by
    have hs := tsupport_unitsExtension_subset f.property.2
    exact ⟨unitsExtension f, contDiff_unitsExtension_of_hasCompactSupport f.property.1 f.property.2,
      (f.property.2.image Units.continuous_val).of_isClosed_subset isClosed_closure hs,
      hs.trans (by rintro _ ⟨g, _, rfl⟩; exact Units.isUnit g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext x
    by_cases hx : IsUnit x
    · obtain ⟨g, rfl⟩ := hx
      exact unitsExtension_val _ g
    · exact (unitsExtension_of_not_isUnit _ hx).trans (f.zero_on_compl hx).symm
  right_inv f := by
    apply Subtype.ext
    funext g
    change unitsExtension (f : Langlands.GeneralLinear n F → ℂ) g.val = f.val g
    exact unitsExtension_val _ g

@[simp] theorem matrixTestFunctionKernelEquiv_apply (f : 𝓓(matrixUnitsOpen F n, ℂ))
    (g : Langlands.GeneralLinear n F) :
    (matrixTestFunctionKernelEquiv f : Langlands.GeneralLinear n F → ℂ) g = f g.val := rfl

@[simp] theorem matrixTestFunctionKernelEquiv_symm_apply
    (f : smoothCompactKernels (Matrix (Fin n) (Fin n) F) (Langlands.GeneralLinear n F))
    (x : Matrix (Fin n) (Fin n) F) :
    matrixTestFunctionKernelEquiv.symm f x = unitsExtension f x := rfl

/-- Derivative along the tangent vectors of the curves `exp(tX) x`. -/
def matrixLeftTestDerivative (X : Matrix (Fin n) (Fin n) F) :
    𝓓(matrixUnitsOpen F n, ℂ) →L[ℂ] 𝓓(matrixUnitsOpen F n, ℂ) :=
  Analysis.testVectorFieldDerivative (fun x => X * x) (contDiff_const.mul contDiff_id)

/-- Derivative along the tangent vectors of the curves `x exp(tX)`. -/
def matrixRightTestDerivative (X : Matrix (Fin n) (Fin n) F) :
    𝓓(matrixUnitsOpen F n, ℂ) →L[ℂ] 𝓓(matrixUnitsOpen F n, ℂ) :=
  Analysis.testVectorFieldDerivative (fun x => x * X) (contDiff_id.mul contDiff_const)

@[simp] theorem matrixLeftTestDerivative_apply (X x : Matrix (Fin n) (Fin n) F)
    (f : 𝓓(matrixUnitsOpen F n, ℂ)) :
    matrixLeftTestDerivative X f x = fderiv ℝ (f : _ → ℂ) x (X * x) := rfl

@[simp] theorem matrixRightTestDerivative_apply (X x : Matrix (Fin n) (Fin n) F)
    (f : 𝓓(matrixUnitsOpen F n, ℂ)) :
    matrixRightTestDerivative X f x = fderiv ℝ (f : _ → ℂ) x (x * X) := rfl

theorem tsupport_matrixLeftTestDerivative_subset (X : Matrix (Fin n) (Fin n) F)
    (f : 𝓓(matrixUnitsOpen F n, ℂ)) :
    tsupport (matrixLeftTestDerivative X f : _ → ℂ) ⊆ tsupport f :=
  Analysis.tsupport_testVectorFieldDerivative_subset _ _ _

theorem tsupport_matrixRightTestDerivative_subset (X : Matrix (Fin n) (Fin n) F)
    (f : 𝓓(matrixUnitsOpen F n, ℂ)) :
    tsupport (matrixRightTestDerivative X f : _ → ℂ) ⊆ tsupport f :=
  Analysis.tsupport_testVectorFieldDerivative_subset _ _ _

end Langlands.Archimedean
