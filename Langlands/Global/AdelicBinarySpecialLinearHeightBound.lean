import Langlands.Global.PrimitiveAdelicGL2
import Langlands.Global.AdelicOrbitHeightMinimum
import Langlands.GroupScheme.SpecialLinear

/-! # A uniform height bound on actual binary special-linear rational orbits -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.BinarySpecialLinearHeight

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]

local notation "SLG" => SpecialLinear.groupScheme (Fin 2) (CommRingCat.of F)

/-- The standard two-dimensional representation of the actual special-linear group scheme. -/
def standardRepresentation : MatrixRepresentation SLG (Fin 2) :=
  SpecialLinear.inclusion (Fin 2) (CommRingCat.of F)

omit [NumberField F] in
/-- The actual affine matrix of this representation is the usual determinant-one inclusion. -/
theorem standardRepresentation_affineMatrix (S : CommAlgCat.{u} F)
    (x : (SLG).affinePoints S) :
    (standardRepresentation F).affineMatrix S x =
      Matrix.SpecialLinearGroup.toGL
        (SpecialLinear.affinePointsEquiv (Fin 2) (CommRingCat.of F) S x) :=
  Corepresented.groupSchemeMap_affinePoints
    (SpecialLinear.corepresentableBy (Fin 2) (CommRingCat.of F))
    (GeneralLinear.corepresentableBy (Fin 2) (CommRingCat.of F))
    SpecialLinear.toGeneralLinear x

/-- The adelic representation uses exactly the determinant-one matrix of the actual point. -/
theorem adelicMatrix_eq_toGL (g : AdelicGroupPoints F SLG) :
    adelicMatrix F SLG (standardRepresentation F) g =
      Matrix.SpecialLinearGroup.toGL
        (SpecialLinear.affinePointsEquiv (Fin 2) (CommRingCat.of F)
          (CommAlgCat.of F (Adeles F)) g) :=
  standardRepresentation_affineMatrix F _ g

/-- The determinant of the actual adelic standard representation is one as an idele. -/
theorem det_adelicMatrix (g : AdelicGroupPoints F SLG) :
    Matrix.GeneralLinearGroup.det (adelicMatrix F SLG (standardRepresentation F) g) = 1 := by
  rw [adelicMatrix_eq_toGL]
  apply Units.ext
  exact (SpecialLinear.affinePointsEquiv (Fin 2) (CommRingCat.of F)
    (CommAlgCat.of F (Adeles F)) g).property

omit [NumberField F] in
/-- Every nonzero rational binary vector is the first column of a determinant-one matrix. -/
theorem exists_specialLinear_firstColumn (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1 = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> assumption
    refine ⟨⟨![![v 0, -(v 1)⁻¹], ![v 1, 0]], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0, h1]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨![![v 0, 0], ![v 1, (v 0)⁻¹]], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A uniform bound on the selected-vector height after translation by an actual rational
special-linear point. The constant is independent of the adelic point. -/
def HasUniformRationalOrbitHeightBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : AdelicGroupPoints F SLG,
    ∃ q : RationalGroupPoints F SLG,
      orbitHeight F SLG (standardRepresentation F) (Pi.single 0 1)
        (g * rational F SLG q) ≤ C

/-- The actual binary special-linear rational orbit has a uniform height bound, with no
compactness or reduction-theory premise. -/
theorem hasUniformRationalOrbitHeightBound : HasUniformRationalOrbitHeightBound F := by
  obtain ⟨C, hC, hherm⟩ := PrimitiveAdelicHeight.exists_rationalHeight_le_sqrt_det F
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨v, hv, hbound⟩ := hherm (adelicMatrix F SLG (standardRepresentation F) g)
  rw [det_adelicMatrix, map_one] at hbound
  simp only [Units.val_one, NNReal.coe_one, Real.sqrt_one, mul_one] at hbound
  obtain ⟨γ, hγ⟩ := exists_specialLinear_firstColumn F v hv
  let q : RationalGroupPoints F SLG :=
    (SpecialLinear.affinePointsEquiv (Fin 2) (CommRingCat.of F)
      (CommAlgCat.of F F)).symm γ
  have hq : (rationalMatrix F SLG (standardRepresentation F) q).val *ᵥ Pi.single 0 1 = v := by
    change ((standardRepresentation F).affineMatrix (CommAlgCat.of F F) q).val *ᵥ _ = v
    rw [standardRepresentation_affineMatrix, show
      SpecialLinear.affinePointsEquiv (Fin 2) (CommRingCat.of F)
        (CommAlgCat.of F F) q = γ from MulEquiv.apply_symm_apply _ _]
    exact hγ
  refine ⟨q, ?_⟩
  rw [orbitHeight_mul_rational, hq]
  exact hbound

/-- The same constant bounds every approximate rational-orbit minimum, multiplied by its
nonnegative approximation factor. -/
theorem exists_uniform_bound_on_approximate_minima :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ), 0 ≤ c →
      ∀ g : AdelicGroupPoints F SLG,
        (∀ q : RationalGroupPoints F SLG,
          orbitHeight F SLG (standardRepresentation F) (Pi.single 0 1) g ≤
            c * orbitHeight F SLG (standardRepresentation F) (Pi.single 0 1)
              (g * rational F SLG q)) →
        orbitHeight F SLG (standardRepresentation F) (Pi.single 0 1) g ≤ c * C := by
  obtain ⟨C, hC, hbound⟩ := hasUniformRationalOrbitHeightBound F
  refine ⟨C, hC, fun c hc g hmin => ?_⟩
  obtain ⟨q, hq⟩ := hbound g
  exact (hmin q).trans (mul_le_mul_of_nonneg_left hq hc)

end Langlands.Global.BinarySpecialLinearHeight
