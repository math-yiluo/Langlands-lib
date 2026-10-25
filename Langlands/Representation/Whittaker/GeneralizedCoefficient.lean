import Langlands.Representation.Character.TransportProof
import Langlands.Representation.Hecke.ActionLocalUnits
import Langlands.HarmonicAnalysis.Distribution.Basic

/-! # Generalized matrix coefficients from algebraic functionals -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulRightInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Applying the full transpose of an integrated operator smooths any algebraic
functional. The result is linear in the functional and the test function. -/
def smoothFunctional :
    Module.Dual ℂ V →ₗ[ℂ] SchwartzBruhat G →ₗ[ℂ] SmoothDual ρ where
  toFun ℓ :=
    { toFun := fun f =>
        ⟨(Hecke.integratedAction μ ρ hρ f).dualMap ℓ,
          Character.integratedAction_dualMap_range_le_smoothVectors μ ρ hρ f
            ⟨ℓ, rfl⟩⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        ext v
        simp [map_add]
      map_smul' := by
        intro c f
        apply Subtype.ext
        ext v
        simp [map_smul] }
  map_add' := by
    intro ℓ₁ ℓ₂
    ext f v
    rfl
  map_smul' := by
    intro c ℓ
    ext f v
    rfl

@[simp]
theorem smoothFunctional_apply (ℓ : Module.Dual ℂ V)
    (f : SchwartzBruhat G) (v : V) :
    smoothDualPairing ρ (smoothFunctional μ ρ hρ ℓ f) v =
      ℓ (Hecke.integratedAction μ ρ hρ f v) := rfl

/-- Generalized matrix coefficient: evaluate the smoothed first functional by an
arbitrary algebraic functional on the actual smooth dual. -/
def generalizedCoefficient :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ (SmoothDual ρ) →ₗ[ℂ] Distribution G where
  toFun ℓ :=
    { toFun := fun η => η.comp (smoothFunctional μ ρ hρ ℓ)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_add' := by
    intro ℓ₁ ℓ₂
    ext η f
    change η (smoothFunctional μ ρ hρ (ℓ₁ + ℓ₂) f) = _
    simp only [map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.comp_apply]
  map_smul' := by
    intro c ℓ
    ext η f
    change η (smoothFunctional μ ρ hρ (c • ℓ) f) = _
    simp only [map_smul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.comp_apply, RingHom.id_apply]

@[simp]
theorem generalizedCoefficient_apply (ℓ : Module.Dual ℂ V)
    (η : Module.Dual ℂ (SmoothDual ρ)) (f : SchwartzBruhat G) :
    generalizedCoefficient μ ρ hρ ℓ η f =
      η (smoothFunctional μ ρ hρ ℓ f) := rfl

/-- The right-translation convention is `R_b f(x) = f(x*b)`. -/
theorem smoothFunctional_rightTranslate (ℓ : Module.Dual ℂ V)
    (b : G) (f : SchwartzBruhat G) :
    smoothFunctional μ ρ hρ ℓ (Hecke.TestFunction.rightTranslate b f) =
      smoothContragredient ρ b (smoothFunctional μ ρ hρ ℓ f) := by
  apply Subtype.ext
  ext v
  change ℓ (Hecke.integratedAction μ ρ hρ
    (Hecke.TestFunction.rightTranslate b f) v) =
      ℓ (Hecke.integratedAction μ ρ hρ f (ρ b⁻¹ v))
  rw [Character.integratedAction_right_input μ ρ hρ, inv_inv]

theorem generalizedCoefficient_rightTranslate (ℓ : Module.Dual ℂ V)
    (η : Module.Dual ℂ (SmoothDual ρ)) (b : G) (f : SchwartzBruhat G) :
    generalizedCoefficient μ ρ hρ ℓ η (Hecke.TestFunction.rightTranslate b f) =
      generalizedCoefficient μ ρ hρ ℓ (η.comp (smoothContragredient ρ b)) f := by
  simp only [generalizedCoefficient_apply, smoothFunctional_rightTranslate,
    LinearMap.comp_apply]

variable [IsMulLeftInvariant μ]

/-- The left-translation convention is `L_a f(x) = f(a⁻¹*x)`. -/
theorem smoothFunctional_leftTranslate (ℓ : Module.Dual ℂ V)
    (a : G) (f : SchwartzBruhat G) :
    smoothFunctional μ ρ hρ ℓ (Hecke.TestFunction.leftTranslate a f) =
      smoothFunctional μ ρ hρ (ℓ.comp (ρ a)) f := by
  apply Subtype.ext
  ext v
  exact congrArg ℓ (Hecke.integratedAction_leftTranslate μ ρ hρ a f v)

theorem generalizedCoefficient_leftTranslate (ℓ : Module.Dual ℂ V)
    (η : Module.Dual ℂ (SmoothDual ρ)) (a : G) (f : SchwartzBruhat G) :
    generalizedCoefficient μ ρ hρ ℓ η (Hecke.TestFunction.leftTranslate a f) =
      generalizedCoefficient μ ρ hρ (ℓ.comp (ρ a)) η f := by
  simp only [generalizedCoefficient_apply, smoothFunctional_leftTranslate]

/-- Convolution smooths first by its left factor and then by its right factor. -/
theorem smoothFunctional_convolution (ℓ : Module.Dual ℂ V)
    (f g : SchwartzBruhat G) :
    smoothFunctional μ ρ hρ ℓ (Hecke.TestFunction.convolution μ f g) =
      smoothFunctional μ ρ hρ
        (smoothDualPairing ρ (smoothFunctional μ ρ hρ ℓ f)) g := by
  apply Subtype.ext
  ext v
  exact congrArg ℓ (Hecke.integratedAction_convolution μ ρ hρ f g v)

/-- Eigenfunctionals on the representation and its smooth dual give the precise
two-sided translation formula, with the chosen test-function conventions. -/
theorem generalizedCoefficient_biTranslate
    (ℓ : Module.Dual ℂ V) (η : Module.Dual ℂ (SmoothDual ρ))
    (a b : G) (c d : ℂ)
    (hℓ : ℓ.comp (ρ a) = c • ℓ)
    (hη : η.comp (smoothContragredient ρ b) = d • η)
    (f : SchwartzBruhat G) :
    generalizedCoefficient μ ρ hρ ℓ η
        (Hecke.TestFunction.leftTranslate a (Hecke.TestFunction.rightTranslate b f)) =
      (c * d) * generalizedCoefficient μ ρ hρ ℓ η f := by
  rw [generalizedCoefficient_leftTranslate, generalizedCoefficient_rightTranslate, hℓ, hη]
  simp [mul_assoc, mul_left_comm]

/-- Haar local units ensure that smoothing does not lose the first functional. -/
theorem smoothFunctional_eq_zero_iff [IsOpenPosMeasure μ] (ℓ : Module.Dual ℂ V) :
    smoothFunctional μ ρ hρ ℓ = 0 ↔ ℓ = 0 := by
  let : μ.IsHaarMeasure := {}
  constructor
  · intro h
    ext v
    obtain ⟨J, hJ, hv⟩ := Hecke.exists_normalizedIndicator_fixes μ ρ hρ v
    have hf := congrArg
      (fun S : SchwartzBruhat G →ₗ[ℂ] SmoothDual ρ =>
        smoothDualPairing ρ (S (Hecke.HeckeAlgebra.toTestFunction μ
          (Hecke.HeckeAlgebra.normalizedIndicator μ J hJ))) v) h
    change ℓ (Hecke.heckeAction μ ρ hρ
      (Hecke.HeckeAlgebra.normalizedIndicator μ J hJ) v) = 0 at hf
    simpa only [hv, LinearMap.zero_apply] using hf
  · rintro rfl
    exact map_zero _

end Langlands.Whittaker
