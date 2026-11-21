import Langlands.Representation.Archimedean.ComplexBorelTestAverageOnto
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Borel averaging onto the specified smooth complex standard module -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.GaugeDescent (triangularDiagonal triangularDiagonal_val)
open Langlands.GodementJacquet (complexTriangularCoordinates complexTriangularCoordinates_apply)

variable (n : ℕ) (ds : List ComplexCharacterData)

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "GL" => Langlands.GeneralLinear n ℂ
local notation "Borel" => upperTriangularSubgroup n ℂ
local notation "Std" => complexStandardModule n ds
local notation "Ω" => matrixUnitsOpen ℂ n
local notation "Test" => 𝓓(Ω, ℂ)
local notation "weight" => fun j : Fin n => posWeight ds j
local notation "exponent" =>
  fun j : Fin n => 2 * (posExponent ds j + (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)))

/-- The normalized inducing character of precisely the Library's complex standard module. -/
def complexStandardBorelCharacter : Borel →* ℂ where
  toFun b := borelChar weight exponent b.val.val
  map_one' := borelChar_one weight exponent
  map_mul' b c :=
    borelChar_mul weight exponent b.property c.property
      (diag_ne_zero_of_upper b.property b.val.isUnit)
      (diag_ne_zero_of_upper c.property c.val.isUnit)

theorem continuous_complexStandardBorelCharacter :
    Continuous (complexStandardBorelCharacter n ds) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  have hb := (contDiffAt_borelChar weight exponent
    (diag_ne_zero_of_upper b.property b.val.isUnit)).continuousAt
  have hval : Continuous (fun p : Borel => p.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  change ContinuousAt (borelChar weight exponent ∘ fun p : Borel => p.val.val) b
  exact ContinuousAt.comp (f := fun p : Borel => p.val.val) (x := b) hb hval.continuousAt

theorem complexStandardBorelCharacter_eq (b : Borel) :
    complexStandardBorelCharacter n ds b =
      principalSeriesCharacter ℂ n (complexPositionCharacter ds) (triangularDiagonal n ℂ b) := by
  change borelChar weight exponent b.val.val = _
  rw [borelChar, principalSeriesCharacter_eq]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← triangularDiagonal_val b j, borelFactor_eq_unitChar]
  congr 1
  ring

private theorem triangularDiagonal_complexTriangularCoordinates
    (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) :
    triangularDiagonal n ℂ (complexTriangularCoordinates n (a, u)) = a := by
  funext i
  apply Units.ext
  rw [triangularDiagonal_val, complexTriangularCoordinates_apply]
  change (Matrix.diagonal (fun j => (a j : ℂ)) * u.val.val) i i = (a i : ℂ)
  rw [Matrix.diagonal_mul, u.property.2 i, mul_one]

private theorem complexTriangularCoordinates_val
    (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) :
    (complexTriangularCoordinates n (a, u)).val = Iwasawa.diagonalUnits a * u.val := by
  rw [complexTriangularCoordinates_apply]
  rfl

theorem complexStandard_leftBorel (F : Std) (b : Borel) (g : GL) :
    F.val (b.val * g) = complexStandardBorelCharacter n ds b * F.val g := by
  let e := complexTriangularCoordinates n
  let p := e.symm b
  have hb : complexTriangularCoordinates n (p.1, p.2) = b := e.apply_symm_apply b
  rw [← hb, complexTriangularCoordinates_val, complexStandardBorelCharacter_eq,
    triangularDiagonal_complexTriangularCoordinates]
  exact F.property.2 p.1 p.2 g

section Measure

variable [SecondCountableTopology (upperTriangularSubgroup n ℂ)]
  [MeasurableSpace (upperTriangularSubgroup n ℂ)] [BorelSpace (upperTriangularSubgroup n ℂ)]
  (μ : Measure (upperTriangularSubgroup n ℂ)) [μ.IsHaarMeasure]

/-- The compactly supported matrix test averages to a smooth complex standard section
with the exact normalized inducing character of the list. -/
def complexStandardBorelTestMap : Test →ₗ[ℂ] Std where
  toFun f := ⟨fun g => complexBorelMatrixAverage n μ (complexStandardBorelCharacter n ds) f g⁻¹.val, by
    constructor
    · have hInv : ContMDiff (matrixModel ℂ n) (matrixModel ℂ n) ∞ (fun g : GL => g⁻¹) :=
        contMDiff_inv (matrixModel ℂ n) ∞
      have hVal : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, Mat) ∞ (Units.val : GL → Mat) :=
        Units.contMDiff_val
      have hSmooth := contDiffOn_complexBorelMatrixAverage n μ _ (continuous_complexStandardBorelCharacter n ds) f
      exact (contMDiffOn_iff_contDiffOn.mpr hSmooth).comp_contMDiff (hVal.comp hInv)
        (fun g => Units.isUnit g⁻¹)
    · intro a u g
      change complexBorelMatrixAverage n μ (complexStandardBorelCharacter n ds) f
          (Iwasawa.diagonalUnits a * u.val * g)⁻¹.val =
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) a *
          complexBorelMatrixAverage n μ (complexStandardBorelCharacter n ds) f g⁻¹.val
      rw [← complexTriangularCoordinates_val n a u, complexBorelMatrixAverage_inv_mul,
        complexStandardBorelCharacter_eq, triangularDiagonal_complexTriangularCoordinates]⟩
  map_add' f f' := by
    apply Subtype.ext
    funext g
    let η := complexStandardBorelCharacter n ds
    have hη := continuous_complexStandardBorelCharacter n ds
    have hI (h : Test) :=
      integrable_complexBorelMatrixAverage n μ η hη h (hx := Units.isUnit g⁻¹)
    change (∫ b : Borel, η b * (f (g⁻¹.val * b.val.val) + f' (g⁻¹.val * b.val.val)) ∂μ) =
      (∫ b : Borel, η b * f (g⁻¹.val * b.val.val) ∂μ) +
        (∫ b : Borel, η b * f' (g⁻¹.val * b.val.val) ∂μ)
    simp only [mul_add, integral_add (hI f) (hI f')]
  map_smul' z f := by
    apply Subtype.ext
    funext g
    let η := complexStandardBorelCharacter n ds
    change (∫ b : Borel, η b * (z * f (g⁻¹.val * b.val.val)) ∂μ) =
      z * (∫ b : Borel, η b * f (g⁻¹.val * b.val.val) ∂μ)
    rw [← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun b => ?_)
    ring

@[simp]
theorem complexStandardBorelTestMap_apply (f : Test) (g : GL) :
    (complexStandardBorelTestMap n ds μ f).val g =
      complexBorelMatrixAverage n μ (complexStandardBorelCharacter n ds) f g⁻¹.val :=
  rfl

theorem complexStandardBorelTestMap_surjective :
    Function.Surjective (complexStandardBorelTestMap n ds μ) := by
  intro F
  obtain ⟨f, hf⟩ := complexBorelTestAverageOnto n μ (complexStandardBorelCharacter n ds)
    F.val F.property.1 (complexStandard_leftBorel n ds F)
  exact ⟨f, Subtype.ext (funext hf)⟩

end Measure

end Langlands.Archimedean
