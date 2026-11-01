import Langlands.Representation.RankinSelberg.AdjacentRankJacquetEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Langlands.RankinSelberg.AdjacentJacquet

open HarmonicAnalysis Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jacquetLinearTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance jacquetLinearValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance jacquetLinearLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance jacquetLinearT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance jacquetLinearMeasurable : MeasurableSpace F.Carrier := borel _
local instance jacquetLinearBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

/-- The exact normalized opposite-parabolic representation in the host statement. -/
abbrev inducedRepresentation :=
  F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
    ((adjacentRankLowerShape r).blockTensor
      (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))

local notation "ρ" => inducedRepresentation F σ χ

/-- The original-carrier scalar evaluation is linear in the actual induced section. -/
def sectionCoefficientLinear (g : GeneralLinear (r + 2) F.Carrier) :
    (ρ).asModule →ₗ[ℂ] ℂ where
  toFun f := sectionCoefficient F ψ σ ℓ χ f g
  map_add' f h := by
    change ℓ.val (adjacentRankLowerTensorCoordinates V
      (Induction.eval _ _ f g + Induction.eval _ _ h g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    change ℓ.val (adjacentRankLowerTensorCoordinates V
      (c • Induction.eval _ _ f g)) = _
    rw [map_smul, map_smul]
    rfl

@[simp] theorem sectionCoefficientLinear_apply
    (g : GeneralLinear (r + 2) F.Carrier) (f : (ρ).asModule) :
    sectionCoefficientLinear F ψ σ ℓ χ g f = sectionCoefficient F ψ σ ℓ χ f g := rfl

/-- Right translation of an actual induced section evaluates by right multiplication. -/
theorem sectionCoefficient_right (k : GeneralLinear (r + 2) F.Carrier)
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier) :
    sectionCoefficient F ψ σ ℓ χ (ρ k f) g =
      sectionCoefficient F ψ σ ℓ χ f (g * k) := rfl

/-- The literal Jacquet kernel is linear in the original induced section. -/
def integrandLinear (g : GeneralLinear (r + 2) F.Carrier) :
    (ρ).asModule →ₗ[ℂ] ((Fin (r + 1) → F.Carrier) → ℂ) where
  toFun f := integrand F ψ σ ℓ χ f g
  map_add' f h := by
    funext x
    change sectionCoefficientLinear F ψ σ ℓ χ (upperColumn x * g) (f + h) * _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' c f := by
    funext x
    change sectionCoefficientLinear F ψ σ ℓ χ (upperColumn x * g) (c • f) * _ = _
    rw [map_smul, smul_eq_mul, mul_assoc]
    rfl

@[simp] theorem integrandLinear_apply (g : GeneralLinear (r + 2) F.Carrier)
    (f : (ρ).asModule) : integrandLinear F ψ σ ℓ χ g f = integrand F ψ σ ℓ χ f g := rfl

/-- The Jacquet kernel commutes with the exact right action on the host induction. -/
theorem integrand_right (k : GeneralLinear (r + 2) F.Carrier)
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier) :
    integrand F ψ σ ℓ χ (ρ k f) g = integrand F ψ σ ℓ χ f (g * k) := by
  funext x
  unfold integrand
  rw [sectionCoefficient_right, mul_assoc]

/-- The actual scalar Jacquet integral, before imposing its convergence hypothesis. -/
def integral (ν : AdditiveHaarMeasure F.Carrier) (f : (ρ).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) : ℂ :=
  ∫ x, integrand F ψ σ ℓ χ f g x ∂rowMeasure ν (r + 1)

/-- Integrating the exact right-translation identity gives coefficient evaluation. -/
theorem integral_right (ν : AdditiveHaarMeasure F.Carrier)
    (k : GeneralLinear (r + 2) F.Carrier) (f : (ρ).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) :
    integral F ψ σ ℓ χ ν (ρ k f) g = integral F ψ σ ℓ χ ν f (g * k) := by
  unfold integral
  rw [integrand_right]

/-- On any family of actual sections with absolute convergence, scalar integration
is a linear map. The hypothesis is discharged by section spanning in the image proof. -/
def integralLinear (ν : AdditiveHaarMeasure F.Carrier)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (g : GeneralLinear (r + 2) F.Carrier) : (ρ).asModule →ₗ[ℂ] ℂ where
  toFun f := integral F ψ σ ℓ χ ν f g
  map_add' f h := by
    change (∫ x, integrandLinear F ψ σ ℓ χ g (f + h) x ∂_) = _
    simp only [map_add, Pi.add_apply]
    exact integral_add (hI f g) (hI h g)
  map_smul' c f := by
    change (∫ x, integrandLinear F ψ σ ℓ χ g (c • f) x ∂_) = _
    simp only [map_smul, Pi.smul_apply]
    exact integral_smul c _

@[simp] theorem integralLinear_apply (ν : AdditiveHaarMeasure F.Carrier)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (g : GeneralLinear (r + 2) F.Carrier) (f : (ρ).asModule) :
    integralLinear F ψ σ ℓ χ ν hI g f = integral F ψ σ ℓ χ ν f g := rfl

/-- The integral at the identity has exactly the scalar Jacquet coefficients at every g. -/
theorem integralLinear_coefficient (ν : AdditiveHaarMeasure F.Carrier)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier) :
    integralLinear F ψ σ ℓ χ ν hI 1 (ρ g f) = integral F ψ σ ℓ χ ν f g := by
  rw [integralLinear_apply, integral_right, one_mul]

end Langlands.RankinSelberg.AdjacentJacquet
