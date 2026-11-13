import Langlands.GroupScheme.SymplecticInnerForm.InvolutionModel
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart
import Langlands.GroupScheme.SymplecticMatrix.Basic
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Norm-one involution isometries through a symplectic chart along a point of a
splitting field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticInnerForm

open Quaternionic Langlands.CentralSimple Langlands.ReducedNorm

section Chart

variable {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A]
  {L : Type u} [Field L] [Algebra K L]
  {I : Type} [Fintype I] [DecidableEq I]
  {τ : FirstKindInvolution K A}
  (ε : L ⊗[K] A ≃ₐ[L] Matrix (I ⊕ I) (I ⊕ I) L)

/-- The symplectic compatibility of a chart with an involution extends along every
coefficient map. -/
theorem chartAlong_baseChange_mul_J
    (he : ∀ x, ε (τ.baseChange L x) * Matrix.J I L = Matrix.J I L * (ε x).transpose)
    {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) (x : R ⊗[K] A) :
    SpecialLinearInnerForm.chartAlong ε f hf (τ.baseChange R x) * Matrix.J I R =
      Matrix.J I R * (SpecialLinearInnerForm.chartAlong ε f hf x).transpose := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [FirstKindInvolution.baseChange_tmul, SpecialLinearInnerForm.chartAlong_tmul,
      SpecialLinearInnerForm.chartAlong_tmul]
    have h := congrArg (fun M => M.map f) (he (1 ⊗ₜ[K] a))
    simp only [FirstKindInvolution.baseChange_tmul, Matrix.map_mul, Matrix.map_J,
      Matrix.transpose_map] at h
    rw [Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul, h]
  | add x y hx hy =>
    rw [map_add, map_add, Matrix.add_mul, hx, hy, map_add, Matrix.transpose_add,
      Matrix.mul_add]

/-- Through the extended chart, the involution is `M ↦ J Mᵀ J⁻¹ = -(J Mᵀ J)`. -/
theorem chartAlong_baseChange
    (he : ∀ x, ε (τ.baseChange L x) * Matrix.J I L = Matrix.J I L * (ε x).transpose)
    {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) (x : R ⊗[K] A) :
    SpecialLinearInnerForm.chartAlong ε f hf (τ.baseChange R x) =
      -(Matrix.J I R * (SpecialLinearInnerForm.chartAlong ε f hf x).transpose *
        Matrix.J I R) := by
  rw [← chartAlong_baseChange_mul_J ε he f hf x, Matrix.mul_assoc, Matrix.J_squared,
    Matrix.mul_neg, Matrix.mul_one, neg_neg]

/-- A tensor element is an involution isometry exactly when its chart matrix is
symplectic. -/
theorem mul_baseChange_eq_one_iff
    (he : ∀ x, ε (τ.baseChange L x) * Matrix.J I L = Matrix.J I L * (ε x).transpose)
    {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) (x : R ⊗[K] A) :
    x * τ.baseChange R x = 1 ↔
      SpecialLinearInnerForm.chartAlong ε f hf x ∈ Matrix.symplecticGroup I R := by
  have hinj := (SpecialLinearInnerForm.chartAlong_bijective ε f hf).1
  have key : SpecialLinearInnerForm.chartAlong ε f hf (x * τ.baseChange R x) =
      -(SpecialLinearInnerForm.chartAlong ε f hf x * Matrix.J I R *
        (SpecialLinearInnerForm.chartAlong ε f hf x).transpose * Matrix.J I R) := by
    rw [map_mul, chartAlong_baseChange ε he f hf x, Matrix.mul_neg]
    simp only [Matrix.mul_assoc]
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h
    have h2 := congrArg (SpecialLinearInnerForm.chartAlong ε f hf) h
    rw [key, map_one] at h2
    have h3 := congrArg (fun M => -(M * Matrix.J I R)) h2
    simp only [Matrix.neg_mul, Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_neg,
      Matrix.mul_one, neg_neg, Matrix.one_mul] at h3
    rw [Matrix.mul_assoc]
    exact neg_injective h3
  · intro h
    apply hinj
    rw [key, map_one, h, Matrix.J_squared, neg_neg]

end Chart

section Points

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Algebra.IsCentral K A] [IsSimpleRing A]
  {I : Type} [Fintype I] [DecidableEq I]
  {τ : FirstKindInvolution K A}
  (ε : L ⊗[K] A ≃ₐ[L] Matrix (I ⊕ I) (I ⊕ I) L)
  (he : ∀ x, ε (τ.baseChange L x) * Matrix.J I L = Matrix.J I L * (ε x).transpose)

/-- The chart matrix of an ambient tensor unit in the norm-one isometry range. -/
def rangeChartHom {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K L) :
    (SubgroupFunctor.range (normOneAmbientι τ)).carrier V →*
      Matrix.symplecticGroup I ((algΓ (CommRingCat.of K)).obj V).unop where
  toFun x := ⟨SpecialLinearInnerForm.chartAlong ε (SpecialLinearInnerForm.pointScalars s)
      (SpecialLinearInnerForm.pointScalars_comp_algebraMap s)
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V x.1 :
        ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A), by
    have hx := (mem_range_normOneAmbientι_iff τ x.1).1 x.2
    exact (mul_baseChange_eq_one_iff ε he _ _ _).1 ((mem_range_isometryι_iff τ x.1).1 hx.1)⟩
  map_one' := by
    apply Subtype.ext
    show SpecialLinearInnerForm.chartAlong ε _ _
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V 1).val = 1
    rw [map_one, Units.val_one, map_one]
  map_mul' x y := by
    apply Subtype.ext
    show SpecialLinearInnerForm.chartAlong ε _ _
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V (x.1 * y.1)).val =
      SpecialLinearInnerForm.chartAlong ε _ _
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V x.1).val *
        SpecialLinearInnerForm.chartAlong ε _ _
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V y.1).val
    rw [map_mul, Units.val_mul, map_mul]

theorem rangeChartHom_coe {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (x : (SubgroupFunctor.range (normOneAmbientι τ)).carrier V) :
    (rangeChartHom ε he s x : Matrix (I ⊕ I) (I ⊕ I) ((algΓ (CommRingCat.of K)).obj V).unop) =
      SpecialLinearInnerForm.chartAlong ε (SpecialLinearInnerForm.pointScalars s)
        (SpecialLinearInnerForm.pointScalars_comp_algebraMap s)
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V x.1 :
          ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A) :=
  rfl

/-- Every symplectic matrix is the chart matrix of exactly one point of the range: the
inverse chart is an involution isometry, and its reduced norm is the determinant `1`. -/
theorem rangeChartHom_bijective {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K L) : Function.Bijective (rangeChartHom ε he s) := by
  have hbij := SpecialLinearInnerForm.chartAlong_bijective ε
    (SpecialLinearInnerForm.pointScalars s)
    (SpecialLinearInnerForm.pointScalars_comp_algebraMap s)
  constructor
  · intro x y h
    apply Subtype.ext
    apply (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V).injective
    apply Units.ext
    exact hbij.1 (congrArg Subtype.val h)
  · intro g
    let e := AlgEquiv.ofBijective _ hbij
    let u : (((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A)ˣ :=
      Units.map e.symm.toMonoidHom (SymplecticMatrix.toGL g)
    have hu : SpecialLinearInnerForm.chartAlong ε (SpecialLinearInnerForm.pointScalars s)
        (SpecialLinearInnerForm.pointScalars_comp_algebraMap s) (u : _ ⊗[K] A) = g := by
      change e (e.symm (g : Matrix (I ⊕ I) (I ⊕ I) _)) = g
      exact e.apply_symm_apply _
    let y := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V).symm u
    have hyu : FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V y = u :=
      MulEquiv.apply_symm_apply _ _
    have hy : y ∈ (SubgroupFunctor.range (normOneAmbientι τ)).carrier V := by
      refine (mem_range_normOneAmbientι_iff τ y).2 ⟨(mem_range_isometryι_iff τ y).2 ?_, ?_⟩
      · rw [hyu]
        apply (mul_baseChange_eq_one_iff ε he _ _ _).2
        rw [hu]
        exact g.2
      · apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) V).injective
        rw [CentralSimpleUnits.reducedNormHom_points, map_one, hyu]
        apply Units.ext
        rw [reducedNormUnits_val, Units.val_one,
          SpecialLinearInnerForm.reducedNorm_eq_det_chartAlong ε _
            (SpecialLinearInnerForm.pointScalars_comp_algebraMap s), hu]
        exact SymplecticGroup.det_eq_one g.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [rangeChartHom_coe]
    change SpecialLinearInnerForm.chartAlong ε _ _
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V y).val = _
    rw [hyu]
    exact hu

/-- The range points of the ambient inclusion, as symplectic matrices through the chart. -/
def rangeChartEquiv {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L) :
    (SubgroupFunctor.range (normOneAmbientι τ)).carrier V ≃*
      Matrix.symplecticGroup I ((algΓ (CommRingCat.of K)).obj V).unop :=
  MulEquiv.ofBijective (rangeChartHom ε he s) (rangeChartHom_bijective ε he s)

/-- Points of the norm-one involution-isometry group over a point of `Spec L`, as
symplectic matrices through the chart. -/
def normOneChartPoints {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L) :
    (V ⟶ (normOneGroup τ).X) ≃*
      Matrix.symplecticGroup I ((algΓ (CommRingCat.of K)).obj V).unop :=
  (SubgroupFunctor.IsRepresentedBy.pointsEquiv (isRepresentedBy_normOneAmbientι τ) V).trans
    (rangeChartEquiv ε he s)

/-- The chart matrix of a point is the extended chart of its ambient tensor unit. -/
theorem normOneChartPoints_val {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (x : V ⟶ (normOneGroup τ).X) :
    (normOneChartPoints ε he s x :
        Matrix (I ⊕ I) (I ⊕ I) ((algΓ (CommRingCat.of K)).obj V).unop) =
      SpecialLinearInnerForm.chartAlong ε (SpecialLinearInnerForm.pointScalars s)
        (SpecialLinearInnerForm.pointScalars_comp_algebraMap s)
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V
            (x ≫ (normOneAmbientι τ).hom.hom) :
          ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A) :=
  rfl

/-- The chart points are natural in the relative test scheme. -/
theorem normOneChartPoints_naturality {V W : Over (Spec (CommRingCat.of K))} (t : W ⟶ V)
    (s : V ⟶ ringTest K L) (x : V ⟶ (normOneGroup τ).X) :
    normOneChartPoints ε he (t ≫ s) (t ≫ x) =
      SymplecticMatrix.map I t.left.appTop.hom (normOneChartPoints ε he s x) := by
  apply Subtype.ext
  have h := SpecialLinearInnerForm.chartAlong_naturality ε
    (SpecialLinearInnerForm.pointScalars s)
    (SpecialLinearInnerForm.pointScalars_comp_algebraMap s)
    ((algΓ (CommRingCat.of K)).map t).unop.hom
    ((FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V
      (x ≫ (normOneAmbientι τ).hom.hom)).val)
  have hs : SpecialLinearInnerForm.pointScalars (t ≫ s) =
      ((((algΓ (CommRingCat.of K)).map t).unop.hom : _ →+* _)).comp
        (SpecialLinearInnerForm.pointScalars s) :=
    SpecialLinearInnerForm.pointScalars_comp t s
  rw [normOneChartPoints_val, SymplecticMatrix.coe_map, normOneChartPoints_val,
    Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
  refine Eq.trans ?_ h
  rw [SpecialLinearInnerForm.chartAlong_congr ε _ hs]
  rfl

end Points

end Langlands.GroupScheme.SymplecticInnerForm
