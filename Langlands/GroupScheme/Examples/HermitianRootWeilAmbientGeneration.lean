import Langlands.GroupScheme.Examples.HermitianRootWeilDynamics
import Langlands.GroupScheme.Examples.HermitianRootAmbientGeneration
import Langlands.GroupScheme.Examples.SU3WeilAmbientGeneration

/-! # Actual rational generation and images of Weil-restricted weighted Hermitian models -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option maxRecDepth 2048

namespace Langlands.GroupScheme.HermitianRoot.WeilSchemeModel

open SU3Root
open SU3Root.SchemeModel (baseAffineTest)
open SU3Root.WeilSchemeModel (rationalIntermediateEquiv rationalSectionEquiv
  rationalCoefficientEquiv rationalCoefficientEquiv_bar)

variable (F k L : Type u) [Field F] [Field k] [Field L]
  [Algebra F k] [FiniteDimensional F k] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

omit [FiniteDimensional F k] [Fintype Middle] [DecidableEq Middle] in
/-- Evaluation of the actual nested coefficient algebra returns the original weights. -/
theorem rationalCoefficientEquiv_weight (i : Middle) :
    rationalCoefficientEquiv F k L ((tensorForm F k L H (baseAffineTest F)).weight i) =
      H.weight i :=
  (rationalCoefficientEquiv F k L).commutes (H.weight i)

/-- Rational points of the actual restricted scheme are the original weighted determinant-one isometries over L. -/
def rationalMatrixEquiv :
    rationalPoints (groupScheme F k L H w hw) ≃*
      specialUnitarySubgroup H :=
  ((GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L H w hw)).trans
    (pointsEquiv F k L H w hw (baseAffineTest F))).trans
      (specialUnitaryRingEquiv (rationalCoefficientEquiv F k L).toRingEquiv
        (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H))

/-- Actual restricted rational points identify with the original k-rational weighted Hermitian points. -/
def rationalPointsEquiv :
    rationalPoints (groupScheme F k L H w hw) ≃*
      rationalPoints (SchemeModel.groupScheme k L H w hw) :=
  (rationalMatrixEquiv F k L H w hw).trans (SchemeModel.rationalMatrixEquiv k L H w hw).symm

/-- The original upper root family as actual ground-field points of the restricted scheme. -/
def rationalUpper :
    Parameters H →* rationalPoints (groupScheme F k L H w hw) :=
  (rationalMatrixEquiv F k L H w hw).symm.toMonoidHom.comp
    (upperSpecialUnitaryHom H)

/-- The rational matrix of a restricted upper point is the original weighted upper matrix. -/
@[simp] theorem rationalMatrixEquiv_upper (x : Parameters H) :
    (rationalMatrixEquiv F k L H w hw (rationalUpper F k L H w hw x)).1 =
      Parameters.embedding H x :=
  congrArg Subtype.val ((rationalMatrixEquiv F k L H w hw).apply_symm_apply _)

/-- Rational point comparison retains the original upper root point. -/
@[simp] theorem rationalPointsEquiv_rationalUpper
    (x : Parameters H) :
    rationalPointsEquiv F k L H w hw (rationalUpper F k L H w hw x) =
      SchemeModel.rationalUpper k L H w hw x := by
  change (SchemeModel.rationalMatrixEquiv k L H w hw).symm
    (rationalMatrixEquiv F k L H w hw ((rationalMatrixEquiv F k L H w hw).symm _)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Evaluation identifies the actual restricted upper test points with rational upper points. -/
theorem rationalCoeffEquiv_rationalUpper
    (x : Parameters (tensorForm F k L H (baseAffineTest F))) :
    GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L H w hw)
        (rationalUpper F k L H w hw (Parameters.mapEquiv
          (rationalCoefficientEquiv F k L).toRingEquiv
          (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H) x)) =
      upperPoints F k L H w hw (baseAffineTest F) x := by
  apply (pointsEquiv F k L H w hw (baseAffineTest F)).injective
  apply (specialUnitaryRingEquiv (rationalCoefficientEquiv F k L).toRingEquiv
    (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H)).injective
  change rationalMatrixEquiv F k L H w hw (rationalUpper F k L H w hw _) = _
  rw [pointsEquiv_upperPoints, specialUnitaryRingEquiv_upper]
  exact (rationalMatrixEquiv F k L H w hw).apply_symm_apply _

/-- The original upper rational points lie in the actual all-test upper subgroup at the base. -/
theorem rationalUpper_mem_upperFunctor (x : Parameters H) :
    rationalUpper F k L H w hw x ∈ (upperFunctor F k L H w hw).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨y, rfl⟩ := (Parameters.mapEquiv
    (rationalCoefficientEquiv F k L).toRingEquiv
    (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H)).surjective x
  have hb : GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L H w hw)
      (rationalUpper F k L H w hw (Parameters.mapEquiv
        (rationalCoefficientEquiv F k L).toRingEquiv
        (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H) y)) ∈
      (upperFunctor F k L H w hw).carrier (baseAffineTest F) := by
    rw [rationalCoeffEquiv_rationalUpper]
    exact ⟨y, rfl⟩
  have h := (upperFunctor F k L H w hw).comp_mem
    (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).inv hb
  have heq : (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).inv ≫
      GaloisPointComparison.rationalCoeffEquiv F (groupScheme F k L H w hw)
        (rationalUpper F k L H w hw (Parameters.mapEquiv
          (rationalCoefficientEquiv F k L).toRingEquiv
          (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H) y)) =
      rationalUpper F k L H w hw (Parameters.mapEquiv
        (rationalCoefficientEquiv F k L).toRingEquiv
        (rationalCoefficientEquiv_bar F k L) (rationalCoefficientEquiv_weight F k L H) y) := by
    change (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).inv ≫
      ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).hom ≫ _) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rwa [heq] at h

/-- The original upper rational family contracts under the actual transferred cocharacter. -/
theorem rationalUpper_range_le_dynamicUnipotent :
    (rationalUpper F k L H w hw).range ≤
      (Dynamic.unipotent (cocharacter F k L H w hw)).carrier (Over.mk (𝟙 _)) := by
  rintro _ ⟨x, rfl⟩
  exact upperFunctor_le_dynamicUnipotent F k L H w hw _
    (rationalUpper_mem_upperFunctor F k L H w hw x)

/-- Under middle anisotropy, the original upper family normally generates all actual restricted rational points. -/
theorem eq_top_of_normal_upper_range (hH : H.IsAnisotropic)
    (N : Subgroup (rationalPoints (groupScheme F k L H w hw))) [N.Normal]
    (hu : (rationalUpper F k L H w hw).range ≤ N) : N = ⊤ := by
  have htop : N.comap (rationalPointsEquiv F k L H w hw).symm.toMonoidHom = ⊤ := by
    apply SchemeModel.eq_top_of_normal_upper_range k L H w hw hH
    rintro _ ⟨x, rfl⟩
    change (rationalPointsEquiv F k L H w hw).symm (SchemeModel.rationalUpper k L H w hw x) ∈ N
    rw [← rationalPointsEquiv_rationalUpper F k L H w hw, MulEquiv.symm_apply_apply]
    exact hu ⟨x, rfl⟩
  apply top_unique
  intro x _
  have hx : rationalPointsEquiv F k L H w hw x ∈
      N.comap (rationalPointsEquiv F k L H w hw).symm.toMonoidHom := by
    rw [htop]
    trivial
  change (rationalPointsEquiv F k L H w hw).symm (rationalPointsEquiv F k L H w hw x) ∈ N at hx
  simpa only [MulEquiv.symm_apply_apply] using hx

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A normal target subgroup containing the composed upper dynamics contains the full
actual restricted rational image. -/
theorem rationalPoints_range_le_of_upper_dynamic (hH : H.IsAnisotropic)
    (f : groupScheme F k L H w hw ⟶ G) (N : Subgroup (rationalPoints G)) [N.Normal]
    (hu : (Dynamic.unipotent (cocharacter F k L H w hw ≫ f)).carrier (Over.mk (𝟙 _)) ≤ N) :
    (rationalPoints.map f).range ≤ N := by
  have htop : N.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_normal_upper_range F k L H w hw hH
    rintro _ ⟨x, rfl⟩
    exact hu (Dynamic.unipotent_le_comap (cocharacter F k L H w hw) f _
      (rationalUpper_range_le_dynamicUnipotent F k L H w hw ⟨x, rfl⟩))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ N.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- The full actual Weil-restricted anisotropic-middle Hermitian image lies in the target's actual parabolic
elementary subgroup. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup (hH : H.IsAnisotropic)
    (hG : IsConnectedReductive G) (f : groupScheme F k L H w hw ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_upper_dynamic F k L H w hw hH f (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG (cocharacter F k L H w hw ≫ f))

end Langlands.GroupScheme.HermitianRoot.WeilSchemeModel
