import Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Scalar extension of the intrinsic character/root complement -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.LinearAlgebra

/-- Realification of a rationalized abelian group is its real tensor space. -/
def rationalRealTensorEquiv (M : Type*) [AddCommGroup M] :
    (ℝ ⊗[ℚ] (ℚ ⊗[ℤ] M)) ≃ₗ[ℝ] (ℝ ⊗[ℤ] M) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M

@[simp] theorem rationalRealTensorEquiv_tmul {M : Type*} [AddCommGroup M]
    (r : ℝ) (q : ℚ) (m : M) :
    rationalRealTensorEquiv M (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] m)) = (q • r) ⊗ₜ[ℤ] m := rfl

@[simp] theorem rationalRealTensorEquiv_symm_tmul {M : Type*} [AddCommGroup M]
    (r : ℝ) (m : M) :
    (rationalRealTensorEquiv M).symm (r ⊗ₜ[ℤ] m) =
      r ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] m) := rfl

/-- Extension of scalars commutes with the range of a linear map. -/
theorem baseChange_range {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    f.range.baseChange A = (f.baseChange A).range := by
  change (f.range.subtype.baseChange A).range = (f.baseChange A).range
  have hf : f = f.range.subtype.comp f.rangeRestrict := rfl
  conv_rhs => rw [hf, LinearMap.baseChange_comp]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _
    (LinearMap.baseChange_surjective A f.surjective_rangeRestrict))]

/-- The cancellation equivalence identifies extended rational spans with real spans. -/
theorem map_ratSpan_baseChange {M : Type*} [AddCommGroup M] (s : Set M) :
    ((ratSpan s).baseChange ℝ).map (rationalRealTensorEquiv M).toLinearMap =
      Submodule.span ℝ ((fun m : M => (1 : ℝ) ⊗ₜ[ℤ] m) '' s) := by
  simp [ratSpan, Submodule.baseChange_span, Submodule.map_span, Set.image_image,
    rationalRealTensorEquiv]

/-- Cancellation commutes with scalar extension of an integral linear map. -/
theorem rationalRealTensorEquiv_naturality {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (f : M →ₗ[ℤ] N) :
    (rationalRealTensorEquiv N).toLinearMap ∘ₗ (f.baseChange ℚ).baseChange ℝ =
      f.baseChange ℝ ∘ₗ (rationalRealTensorEquiv M).toLinearMap := by
  ext
  simp [rationalRealTensorEquiv]

/-- Cancellation identifies the extended rational image with the real image. -/
theorem map_range_baseChange_rat_real {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (f : M →ₗ[ℤ] N) :
    (((f.baseChange ℚ).range).baseChange ℝ).map
      (rationalRealTensorEquiv N).toLinearMap = (f.baseChange ℝ).range := by
  rw [baseChange_range, ← LinearMap.range_comp, rationalRealTensorEquiv_naturality,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _
      (rationalRealTensorEquiv M).surjective)]

/-- A split direct-sum decomposition remains a direct-sum decomposition after
extension of scalars. No flatness assumption is needed for a split decomposition. -/
theorem isCompl_baseChange {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] {p q : Submodule R M} (h : IsCompl p q) :
    IsCompl (p.baseChange A) (q.baseChange A) := by
  let π := p.projection q h
  have hleft : ∀ x ∈ p.baseChange A, π.baseChange A x = x := by
    rintro x ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a m => simp [π]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hright : ∀ x ∈ q.baseChange A, π.baseChange A x = 0 := by
    rintro x ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a m => simp [π]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro x hp hq
    exact (hleft x hp).symm.trans (hright x hq)
  · apply eq_top_iff.mpr
    intro x hx
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul a m =>
      rw [← Submodule.projection_add_projection_eq_self h m, tmul_add]
      exact add_mem
        (show a ⊗ₜ[R] p.projection q h m ∈ p.baseChange A ⊔ q.baseChange A from
          (show p.baseChange A ≤ p.baseChange A ⊔ q.baseChange A from le_sup_left)
            (Submodule.tmul_mem_baseChange_of_mem a
            (Submodule.projection_apply_mem h m)))
        (show a ⊗ₜ[R] q.projection p h.symm m ∈ p.baseChange A ⊔ q.baseChange A from
          (show q.baseChange A ≤ p.baseChange A ⊔ q.baseChange A from le_sup_right)
            (Submodule.tmul_mem_baseChange_of_mem a
            (Submodule.projection_apply_mem h.symm m)))
    | add x y hx hy => exact add_mem hx hy

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra
open RealTorusSpace TensorProduct.AlgebraTensorModule

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Under the actual tensor-space equivalence, scalar extension of character
restriction has exactly the existing real restriction range. -/
theorem map_rationalCharacterRestrictRat_range_baseChange
    {H : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G) :
    (((rationalCharacterRestrictRat f).range).baseChange ℝ).map
      (rationalRealTensorEquiv (rationalCharacters H)).toLinearMap =
        (rationalCharacterRestrictReal f).range :=
  map_range_baseChange_rat_real (characterRestrict f).toIntLinearMap

variable [IsAffineHom G.X.hom]

/-- Under the actual tensor-space equivalence, scalar extension of all actual
relative roots has exactly the existing real root span. -/
theorem map_relativeRootSpan_baseChange (i : T.toGrp ⟶ G) :
    ((relativeRootSpan i).baseChange ℝ).map
      (rationalRealTensorEquiv (characterLattice T)).toLinearMap =
        relativeRootSpanReal i :=
  map_ratSpan_baseChange (relativeRoots i)

/-- The intrinsic rational complement implies its real counterpart in the
published full real character space. -/
theorem relativeCharacterRootComplementReal_of_rat (i : T.toGrp ⟶ G)
    (h : IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range) :
    IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range := by
  have hc := Submodule.isCompl_map (rationalRealTensorEquiv (characterLattice T))
    (isCompl_baseChange h)
  have hr : (((rationalCharacterRestrictRat i).range).baseChange ℝ).map
      (rationalRealTensorEquiv (characterLattice T)).toLinearMap =
        (rationalCharacterRestrictReal i).range :=
    map_rationalCharacterRestrictRat_range_baseChange i
  simpa only [map_relativeRootSpan_baseChange, hr] using hc

end Langlands.GroupScheme
