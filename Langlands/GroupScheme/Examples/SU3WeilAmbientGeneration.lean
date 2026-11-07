import Langlands.GroupScheme.Examples.SU3WeilDynamics
import Langlands.GroupScheme.Examples.SU3AmbientGeneration

/-! # Actual rational generation and ambient images of Weil-restricted SU3 -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option maxRecDepth 2048

namespace Langlands.GroupScheme.SU3Root.WeilSchemeModel

variable (F k L : Type u) [Field F] [Field k] [Field L]
  [Algebra F k] [FiniteDimensional F k] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Evaluate the actual intermediate tensor algebra at the ground field. -/
def rationalIntermediateEquiv :
    AffineWeil.tensorAlgebra F k (SchemeModel.baseAffineTest F) ≃ₐ[k] k :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k)
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of F) F))).trans
      (Algebra.TensorProduct.rid F k k)

/-- Evaluate the actual sections of the intermediate tensor spectrum. -/
def rationalSectionEquiv :
    SpecialLinear.WeilRoot.sectionAlgebra k
      (tensorTest F k (SchemeModel.baseAffineTest F)) ≃ₐ[k] k :=
  (Corepresented.affineSectionsAlgEquiv
    (AffineWeil.tensorAlgebra F k (SchemeModel.baseAffineTest F))).trans
      (rationalIntermediateEquiv F k)

/-- Recover L from the nested actual coefficient algebra of restricted rational points. -/
def rationalCoefficientEquiv :
    SpecialLinear.WeilRoot.tensorAlgebra k L
      (tensorTest F k (SchemeModel.baseAffineTest F)) ≃ₐ[L] L :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (rationalSectionEquiv F k)).trans (Algebra.TensorProduct.rid k L L)

omit [FiniteDimensional F k] in
/-- Evaluation of the nested sections preserves the original quadratic involution. -/
theorem rationalCoefficientEquiv_bar
    (x : SpecialLinear.WeilRoot.tensorAlgebra k L
      (tensorTest F k (SchemeModel.baseAffineTest F))) :
    rationalCoefficientEquiv F k L
        ((coefficientInvolution F k L (SchemeModel.baseAffineTest F)).bar x) =
      (fieldInvolution k L).bar (rationalCoefficientEquiv F k L x) := by
  let e := (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (rationalSectionEquiv F k)).trans (Algebra.TensorProduct.rid k L L)
  change e (QuasiSplitUnitary.scalarConjugation _ (conjugation k L) x) =
    conjugation k L (e x)
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
    change (rationalSectionEquiv F k r) • conjugation k L a =
      conjugation k L ((rationalSectionEquiv F k r) • a)
    exact (map_smul (conjugation k L) _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Rational points of the actual restricted scheme are the original SU3 matrices over L. -/
def rationalMatrixEquiv :
    rationalPoints (groupScheme F k L) ≃*
      specialUnitarySubgroup (fieldInvolution k L) :=
  ((GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L)).trans
    (pointsEquiv F k L (SchemeModel.baseAffineTest F))).trans
      (specialUnitaryRingEquiv (rationalCoefficientEquiv F k L).toRingEquiv
        (rationalCoefficientEquiv_bar F k L))

/-- Actual restricted rational points identify with the original k-rational SU3 points. -/
def rationalPointsEquiv :
    rationalPoints (groupScheme F k L) ≃*
      rationalPoints (SchemeModel.groupScheme k L) :=
  (rationalMatrixEquiv F k L).trans (SchemeModel.rationalMatrixEquiv k L).symm

/-- The original upper root family as actual ground-field points of the restricted scheme. -/
def rationalUpper :
    Parameters (fieldInvolution k L) →* rationalPoints (groupScheme F k L) :=
  (rationalMatrixEquiv F k L).symm.toMonoidHom.comp
    (upperSpecialUnitaryHom (fieldInvolution k L))

/-- Rational point comparison retains the original upper root point. -/
@[simp] theorem rationalPointsEquiv_rationalUpper
    (x : Parameters (fieldInvolution k L)) :
    rationalPointsEquiv F k L (rationalUpper F k L x) =
      SchemeModel.rationalUpper k L x := by
  change (SchemeModel.rationalMatrixEquiv k L).symm
    (rationalMatrixEquiv F k L ((rationalMatrixEquiv F k L).symm _)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Evaluation identifies the actual restricted upper test points with rational upper points. -/
theorem rationalCoeffEquiv_rationalUpper
    (x : Parameters (coefficientInvolution F k L (SchemeModel.baseAffineTest F))) :
    GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L)
        (rationalUpper F k L (Parameters.mapEquiv
          (rationalCoefficientEquiv F k L).toRingEquiv
          (rationalCoefficientEquiv_bar F k L) x)) =
      upperPoints F k L (SchemeModel.baseAffineTest F) x := by
  apply (pointsEquiv F k L (SchemeModel.baseAffineTest F)).injective
  apply (specialUnitaryRingEquiv (rationalCoefficientEquiv F k L).toRingEquiv
    (rationalCoefficientEquiv_bar F k L)).injective
  change rationalMatrixEquiv F k L (rationalUpper F k L _) = _
  rw [pointsEquiv_upperPoints, specialUnitaryRingEquiv_upper]
  exact (rationalMatrixEquiv F k L).apply_symm_apply _

/-- The original upper rational points lie in the actual all-test upper subgroup at the base. -/
theorem rationalUpper_mem_upperFunctor (x : Parameters (fieldInvolution k L)) :
    rationalUpper F k L x ∈ (upperFunctor F k L).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨y, rfl⟩ := (Parameters.mapEquiv
    (rationalCoefficientEquiv F k L).toRingEquiv
    (rationalCoefficientEquiv_bar F k L)).surjective x
  have hb : GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L)
      (rationalUpper F k L (Parameters.mapEquiv
        (rationalCoefficientEquiv F k L).toRingEquiv
        (rationalCoefficientEquiv_bar F k L) y)) ∈
      (upperFunctor F k L).carrier (SchemeModel.baseAffineTest F) := by
    rw [rationalCoeffEquiv_rationalUpper]
    exact ⟨y, rfl⟩
  have h := (upperFunctor F k L).comp_mem
    (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).inv hb
  have heq : (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).inv ≫
      GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L)
        (rationalUpper F k L (Parameters.mapEquiv
          (rationalCoefficientEquiv F k L).toRingEquiv
          (rationalCoefficientEquiv_bar F k L) y)) =
      rationalUpper F k L (Parameters.mapEquiv
        (rationalCoefficientEquiv F k L).toRingEquiv
        (rationalCoefficientEquiv_bar F k L) y) := by
    change (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).inv ≫
      ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).hom ≫ _) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rwa [heq] at h

/-- The original upper rational family contracts under the actual transferred cocharacter. -/
theorem rationalUpper_range_le_dynamicUnipotent :
    (rationalUpper F k L).range ≤
      (Dynamic.unipotent (cocharacter F k L)).carrier (Over.mk (𝟙 _)) := by
  rintro _ ⟨x, rfl⟩
  exact upperFunctor_le_dynamicUnipotent F k L _
    (rationalUpper_mem_upperFunctor F k L x)

/-- The original upper family normally generates all actual restricted rational points. -/
theorem eq_top_of_normal_upper_range
    (N : Subgroup (rationalPoints (groupScheme F k L))) [N.Normal]
    (hu : (rationalUpper F k L).range ≤ N) : N = ⊤ := by
  have htop : N.comap (rationalPointsEquiv F k L).symm.toMonoidHom = ⊤ := by
    apply SchemeModel.eq_top_of_normal_upper_range k L
    rintro _ ⟨x, rfl⟩
    change (rationalPointsEquiv F k L).symm (SchemeModel.rationalUpper k L x) ∈ N
    rw [← rationalPointsEquiv_rationalUpper F k L, MulEquiv.symm_apply_apply]
    exact hu ⟨x, rfl⟩
  apply top_unique
  intro x _
  have hx : rationalPointsEquiv F k L x ∈
      N.comap (rationalPointsEquiv F k L).symm.toMonoidHom := by
    rw [htop]
    trivial
  change (rationalPointsEquiv F k L).symm (rationalPointsEquiv F k L x) ∈ N at hx
  simpa only [MulEquiv.symm_apply_apply] using hx

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A normal target subgroup containing the composed upper dynamics contains the full
actual restricted rational image. -/
theorem rationalPoints_range_le_of_upper_dynamic
    (f : groupScheme F k L ⟶ G) (N : Subgroup (rationalPoints G)) [N.Normal]
    (hu : (Dynamic.unipotent (cocharacter F k L ≫ f)).carrier (Over.mk (𝟙 _)) ≤ N) :
    (rationalPoints.map f).range ≤ N := by
  have htop : N.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_normal_upper_range F k L
    rintro _ ⟨x, rfl⟩
    exact hu (Dynamic.unipotent_le_comap (cocharacter F k L) f _
      (rationalUpper_range_le_dynamicUnipotent F k L ⟨x, rfl⟩))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ N.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- The full actual Weil-restricted SU3 image lies in the target's actual parabolic
elementary subgroup. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup
    (hG : IsConnectedReductive G) (f : groupScheme F k L ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_upper_dynamic F k L f (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG (cocharacter F k L ≫ f))

end Langlands.GroupScheme.SU3Root.WeilSchemeModel
