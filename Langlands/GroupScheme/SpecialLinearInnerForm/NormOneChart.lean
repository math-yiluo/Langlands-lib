import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.Algebra.ReducedNormFiniteChart
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # Reduced-norm-one points through a matrix chart along a point of a splitting field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearInnerForm

open Langlands.CentralSimple Langlands.ReducedNorm

section Chart

variable {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A]
  {L : Type u} [Field L] [Algebra K L]
  {I : Type} [Fintype I] [DecidableEq I]
  (ε : L ⊗[K] A ≃ₐ[L] Matrix I I L)

/-- Extend a matrix chart of `A` along a ring homomorphism `f : L → R` over `K`. -/
def chartAlong {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) : R ⊗[K] A →ₐ[R] Matrix I I R :=
  letI : Algebra L R := f.toAlgebra
  haveI : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq' hf.symm
  splittingMap ε R

theorem chartAlong_tmul {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) (r : R) (a : A) :
    chartAlong ε f hf (r ⊗ₜ[K] a) = r • (ε (1 ⊗ₜ[K] a)).map f :=
  rfl

/-- The canonical reduced norm is the determinant of the extended chart. -/
theorem reducedNorm_eq_det_chartAlong [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) (x : R ⊗[K] A) :
    reducedNorm K A R x = (chartAlong ε f hf x).det := by
  let _ : Algebra L R := f.toAlgebra
  have : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq' hf.symm
  exact reducedNorm_eq_det_fintype K A ε R x

theorem chartAlong_bijective {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) :
    Function.Bijective (chartAlong ε f hf) := by
  let _ : Algebra L R := f.toAlgebra
  have : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq' hf.symm
  exact (extendSplittingChart ε R).bijective

theorem chartAlong_congr {R : Type u} [CommRing R] [Algebra K R] {f₁ f₂ : L →+* R}
    (h₁ : f₁.comp (algebraMap K L) = algebraMap K R) (h : f₁ = f₂) :
    chartAlong ε f₁ h₁ = chartAlong ε f₂ (h ▸ h₁) := by
  subst h
  rfl

/-- The extended chart is natural in the coefficient algebra. -/
theorem chartAlong_naturality {R S : Type u} [CommRing R] [CommRing S] [Algebra K R]
    [Algebra K S] (f : L →+* R) (hf : f.comp (algebraMap K L) = algebraMap K R)
    (g : R →ₐ[K] S) (x : R ⊗[K] A) :
    chartAlong ε ((g : R →+* S).comp f)
        (by rw [RingHom.comp_assoc, hf]; exact g.comp_algebraMap)
        (Algebra.TensorProduct.map g (AlgHom.id K A) x) =
      (chartAlong ε f hf x).map g := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [Algebra.TensorProduct.map_tmul, chartAlong_tmul, chartAlong_tmul]
    ext i j
    simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext i j
    simp

/-- The extended chart identifies reduced-norm-one units with determinant-one matrices. -/
def chartUnitsEquiv [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) :
    reducedNormOne K A R ≃* Matrix.SpecialLinearGroup I R where
  toFun x := ⟨chartAlong ε f hf (x.val : R ⊗[K] A), by
    rw [← reducedNorm_eq_det_chartAlong]
    exact (mem_reducedNormOne K A R x.val).mp x.property⟩
  invFun g := ⟨Units.map
      (AlgEquiv.ofBijective (chartAlong ε f hf)
        (chartAlong_bijective ε f hf)).symm.toMonoidHom
      (Matrix.SpecialLinearGroup.toGL g), by
    rw [mem_reducedNormOne, reducedNorm_eq_det_chartAlong ε f hf]
    change (chartAlong ε f hf ((AlgEquiv.ofBijective (chartAlong ε f hf)
      (chartAlong_bijective ε f hf)).symm (g : Matrix I I R))).det = 1
    rw [← AlgEquiv.ofBijective_apply _ (chartAlong_bijective ε f hf),
      AlgEquiv.apply_symm_apply]
    exact g.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    exact (AlgEquiv.ofBijective (chartAlong ε f hf) (chartAlong_bijective ε f hf)).symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    exact (AlgEquiv.ofBijective (chartAlong ε f hf) (chartAlong_bijective ε f hf)).apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    exact _root_.map_mul (chartAlong ε f hf) _ _

@[simp] theorem chartUnitsEquiv_val [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
    (hf : f.comp (algebraMap K L) = algebraMap K R) (x : reducedNormOne K A R) :
    (chartUnitsEquiv ε f hf x : Matrix I I R) = chartAlong ε f hf (x.val : R ⊗[K] A) :=
  rfl

end Chart

section Points

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- The scalar map `L → Γ(V)` of a relative point `V → Spec L` over `Spec K`. -/
def pointScalars {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L) :
    L →+* ((algΓ (CommRingCat.of K)).obj V).unop :=
  ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ s.left.appTop).hom

theorem pointScalars_comp_algebraMap {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K L) :
    (pointScalars s).comp (algebraMap K L) =
      algebraMap K ((algΓ (CommRingCat.of K)).obj V).unop := by
  apply RingHom.ext
  intro r
  change s.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap K L r)) =
    V.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)
  rw [← Over.w s]
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.left.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap K L))) r)

/-- Restricting a point along a test morphism composes its scalar map with the pullback. -/
theorem pointScalars_comp {V W : Over (Spec (CommRingCat.of K))} (t : W ⟶ V)
    (s : V ⟶ ringTest K L) :
    pointScalars (t ≫ s) = t.left.appTop.hom.comp (pointScalars s) := by
  apply RingHom.ext
  intro l
  change (t.left ≫ s.left).appTop _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Precomposing a point with the spectrum of a Galois automorphism precomposes its scalars. -/
theorem pointScalars_comp_ringTestMap {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K L) (σ : L ≃ₐ[K] L) :
    pointScalars (s ≫ ringTestMap K σ.toAlgHom) = (pointScalars s).comp (σ : L →+* L) := by
  apply RingHom.ext
  intro l
  change (s.left ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l) = _
  rw [Scheme.Hom.comp_appTop]
  change s.left.appTop ((Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) =
    s.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (σ l))
  congr 1
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom σ.toAlgHom.toRingHom)) l).symm

variable {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Algebra.IsCentral K A] [IsSimpleRing A]
  {I : Type} [Fintype I] [DecidableEq I]
  (ε : L ⊗[K] A ≃ₐ[L] Matrix I I L)

/-- Points of the reduced-norm-one group over a point of `Spec L`, as determinant-one
matrices through the chart. -/
def normOneChartPoints {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L) :
    (V ⟶ (CentralSimpleUnits.normOne K A).X) ≃*
      Matrix.SpecialLinearGroup I ((algΓ (CommRingCat.of K)).obj V).unop :=
  (CentralSimpleUnits.normOnePointsEquiv K A V).trans
    (chartUnitsEquiv ε (pointScalars s) (pointScalars_comp_algebraMap s))

theorem normOneChartPoints_val {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (x : V ⟶ (CentralSimpleUnits.normOne K A).X) :
    (normOneChartPoints ε s x : Matrix I I _) =
      chartAlong ε (pointScalars s) (pointScalars_comp_algebraMap s)
        ((CentralSimpleUnits.normOnePointsEquiv K A V x).val :
          ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A) :=
  rfl

/-- The chart points are natural in the relative test scheme. -/
theorem normOneChartPoints_naturality {V W : Over (Spec (CommRingCat.of K))} (t : W ⟶ V)
    (s : V ⟶ ringTest K L) (x : V ⟶ (CentralSimpleUnits.normOne K A).X) :
    normOneChartPoints ε (t ≫ s) (t ≫ x) =
      Matrix.SpecialLinearGroup.map t.left.appTop.hom (normOneChartPoints ε s x) := by
  apply Subtype.ext
  have h := chartAlong_naturality ε (pointScalars s) (pointScalars_comp_algebraMap s)
    ((algΓ (CommRingCat.of K)).map t).unop.hom
    ((CentralSimpleUnits.normOnePointsEquiv K A V x).val :
      ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A)
  have hs : pointScalars (t ≫ s) =
      ((((algΓ (CommRingCat.of K)).map t).unop.hom : _ →+* _)).comp (pointScalars s) :=
    pointScalars_comp t s
  rw [normOneChartPoints_val, CentralSimpleUnits.normOnePointsEquiv_naturality]
  refine Eq.trans ?_ h
  rw [chartAlong_congr ε _ hs]
  rfl

end Points

end Langlands.GroupScheme.SpecialLinearInnerForm
