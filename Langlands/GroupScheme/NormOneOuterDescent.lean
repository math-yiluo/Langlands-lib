import Langlands.Algebra.GaloisAlgebraDescent
import Langlands.Algebra.ReducedNormFiniteChart
import Langlands.GroupScheme.SpecialLinearInnerForm.ConjugationDescent

/-! # Opposite algebras from equivariant outer norm-one matrix formulas -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.GroupScheme.NormOneOuterDescent

open Langlands.CentralSimple Langlands.GaloisAlgebraDescent

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    (L : Type v) [Field L] [Algebra K L]

/-- Coefficient conjugation preserves the actual reduced-norm-one tensor units. -/
def coefficientConjugateNormOne (σ : L ≃ₐ[K] L) :
    reducedNormOne K A L →* reducedNormOne K A L where
  toFun x := ⟨Units.map (coefficientConjugate K L A σ).toMonoidHom x.val, by
    rw [mem_reducedNormOne]
    change reducedNorm K A L
      (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
        (x.val : L ⊗[K] A)) = 1
    rw [reducedNorm_naturality, (mem_reducedNormOne K A L x.val).mp x.property,
      map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp]
theorem coefficientConjugateNormOne_val (σ : L ≃ₐ[K] L)
    (x : reducedNormOne K A L) :
    ((coefficientConjugateNormOne K A L σ x).val : L ⊗[K] A) =
      coefficientConjugate K L A σ (x.val : L ⊗[K] A) := rfl

variable {I : Type*} [Fintype I] [DecidableEq I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)

/-- Over the splitting field itself, the chart gives the determinant-one group
without any further coefficient identifications. -/
def chartNormOneEquiv :
    reducedNormOne K A L ≃* Matrix.SpecialLinearGroup I L where
  toFun x := ⟨e (x.val : L ⊗[K] A), by
    rw [← reducedNorm_eq_chart_det_fintype K A e]
    exact (mem_reducedNormOne K A L x.val).mp x.property⟩
  invFun g := ⟨Units.map e.symm.toMonoidHom (Matrix.SpecialLinearGroup.toGL g), by
    rw [mem_reducedNormOne, reducedNorm_eq_chart_det_fintype K A e]
    change (e (e.symm (g : Matrix I I L))).det = 1
    rw [AlgEquiv.apply_symm_apply]
    exact g.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    exact e.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    exact e.apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul e _ _

@[simp]
theorem chartNormOneEquiv_val (x : reducedNormOne K A L) :
    (chartNormOneEquiv K A L e x : Matrix I I L) =
      e (x.val : L ⊗[K] A) := rfl

@[simp]
theorem chartNormOneEquiv_symm_val (g : Matrix.SpecialLinearGroup I L) :
    ((chartNormOneEquiv K A L e).symm g).val =
      Units.map e.symm.toMonoidHom (Matrix.SpecialLinearGroup.toGL g) := rfl

include e in
/-- Norm-one tensor units span the scalar-extended algebra over every splitting
field, in all matrix sizes and characteristics. -/
theorem span_normOne :
    Submodule.span L (Set.range (fun x : reducedNormOne K A L =>
      (x.val : L ⊗[K] A))) = ⊤ := by
  apply top_unique
  intro x _
  have hx : e x ∈ Submodule.span L
      (Set.range (fun g : Matrix.SpecialLinearGroup I L => (g : Matrix I I L))) := by
    rw [SpecialLinearInnerForm.span_specialLinear]
    trivial
  have hx' : e.symm (e x) ∈ Submodule.span L
      (Set.range (fun x : reducedNormOne K A L => (x.val : L ⊗[K] A))) := by
    generalize e x = y at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact Submodule.subset_span ⟨(chartNormOneEquiv K A L e).symm g, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul l x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ l hx
  simpa only [AlgEquiv.symm_apply_apply] using hx'

/-- Matrix conjugation as an algebra equivalence. -/
def conjugationAlgEquiv (H : GL I L) : Matrix I I L ≃ₐ[L] Matrix I I L where
  __ := SpecialLinearInnerForm.conjugationAlgHom (R := L) H
  invFun := SpecialLinearInnerForm.conjugationAlgHom (R := L) H⁻¹
  left_inv X := by simp [SpecialLinearInnerForm.conjugationAlgHom, mul_assoc]
  right_inv X := by simp [SpecialLinearInnerForm.conjugationAlgHom, mul_assoc]

@[simp]
theorem conjugationAlgEquiv_apply (H : GL I L) (X : Matrix I I L) :
    conjugationAlgEquiv L H X =
      (H : Matrix I I L) * X * ((H⁻¹ : GL I L) : Matrix I I L) := rfl

omit [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] in
/-- The algebra anti-equivalence underlying an outer matrix formula. -/
def outerAntiEquiv (H : GL I L) : L ⊗[K] A ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ :=
  e.trans ((Matrix.transposeAlgEquiv (R := L) (m := I) (α := L)).trans
    (AlgEquiv.op ((conjugationAlgEquiv L H).trans e.symm)))

omit [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] in
/-- The anti-equivalence acts by conjugated transpose in the splitting chart. -/
theorem chart_outerAntiEquiv (H : GL I L) (x : L ⊗[K] A) :
    e (outerAntiEquiv K A L e H x).unop =
      (H : Matrix I I L) * (e x).transpose * ((H⁻¹ : GL I L) : Matrix I I L) := by
  simp [outerAntiEquiv]

variable (α : reducedNormOne K A L ≃* reducedNormOne K A L) (H : GL I L)
    (houter : ∀ x : reducedNormOne K A L,
      e ((α x).val : L ⊗[K] A) =
        (H : Matrix I I L) * (e ((x⁻¹).val : L ⊗[K] A)).transpose *
          ((H⁻¹ : GL I L) : Matrix I I L))

include houter

/-- On norm-one elements, the anti-equivalence is the group automorphism
composed with inversion. -/
theorem outerAntiEquiv_normOne (x : reducedNormOne K A L) :
    (outerAntiEquiv K A L e H (x.val : L ⊗[K] A)).unop =
      ((α x⁻¹).val : L ⊗[K] A) := by
  apply e.injective
  rw [chart_outerAntiEquiv, houter]
  simp only [inv_inv]

variable (hcov : ∀ (σ : L ≃ₐ[K] L) (x : reducedNormOne K A L),
    α (coefficientConjugateNormOne K A L σ x) =
      coefficientConjugateNormOne K A L σ (α x))

include hcov

/-- Covariance of the norm-one group automorphism determines covariance of the
anti-equivalence on the entire scalar-extended algebra. -/
theorem outerAntiEquiv_equivariant (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    coefficientConjugate K L A σ (outerAntiEquiv K A L e H x).unop =
      (outerAntiEquiv K A L e H (coefficientConjugate K L A σ x)).unop := by
  have hx : x ∈ Submodule.span L (Set.range
      (fun u : reducedNormOne K A L => (u.val : L ⊗[K] A))) := by
    rw [span_normOne K A L e]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    rw [outerAntiEquiv_normOne K A L e α H houter]
    rw [← coefficientConjugateNormOne_val K A L σ u,
      outerAntiEquiv_normOne K A L e α H houter]
    change ((coefficientConjugateNormOne K A L σ (α u⁻¹)).val : L ⊗[K] A) =
      ((α (coefficientConjugateNormOne K A L σ u)⁻¹).val : L ⊗[K] A)
    rw [← map_inv]
    exact congrArg (fun v : reducedNormOne K A L => (v.val : L ⊗[K] A))
      (hcov σ u⁻¹).symm
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]
  | smul l x _ hx =>
    simp only [map_smul, MulOpposite.unop_smul, coefficientConjugate_smul, hx]

/-- An outer matrix formula for a Galois-covariant norm-one automorphism
supplies a scalar-fixing equivalence with the opposite algebra. -/
def oppositeEquivOfOuter [FiniteDimensional K L] [IsGalois K L] :
    A ≃ₐ[K] Aᵐᵒᵖ :=
  descendOppositeEquiv K L A (outerAntiEquiv K A L e H)
    (outerAntiEquiv_equivariant K A L e α H houter hcov)

end Langlands.GroupScheme.NormOneOuterDescent
