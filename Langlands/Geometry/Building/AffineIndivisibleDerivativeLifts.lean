import Langlands.Geometry.Building.AffineTransitiveRootLengths
import Langlands.Geometry.Building.AffineRootSystemPullback
import Langlands.Geometry.Building.AffineRootSystemTransport

/-! # Integral affine models and transport of indivisible derivative lifts -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uW uB

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {W : Type uW} {B : Type uB}
  [AddCommGroup W] [Module ℝ W] [AddTorsor W B]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (Module.Dual ℝ V)}

/-- At the chosen origin, the affine roots are all integer translates of
exactly the specified linear forms. No reducedness condition is imposed. -/
def HasIntegralConstantDescription (Ψ : Set (A →ᵃ[ℝ] ℝ))
    (Φ : Set (Module.Dual ℝ V)) (x₀ : A) : Prop :=
  ∀ ψ : A →ᵃ[ℝ] ℝ,
    ψ ∈ Ψ ↔ ψ.linear ∈ Φ ∧ ∃ n : ℤ, ψ x₀ = (n : ℝ)

/-- A reduced set of affine roots has indivisible lifts of every derivative. -/
theorem HasIndivisibleDerivativeLifts.of_isReduced (hΨ : IsReduced Ψ) :
    HasIndivisibleDerivativeLifts Ψ := by
  rintro ⟨a, ψ, hψ, hlin⟩
  exact ⟨ψ, (nonDivisibleRoots_eq_self_iff.mpr hΨ).symm ▸ hψ, hlin⟩

/-- A root taking value one at an origin is indivisible if every root has
integer value there. -/
theorem mem_nonDivisibleRoots_of_apply_eq_one
    (x₀ : A) (hintegral : ∀ ψ ∈ Ψ, ∃ n : ℤ, ψ x₀ = (n : ℝ))
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (hvalue : ψ x₀ = 1) :
    ψ ∈ nonDivisibleRoots Ψ := by
  refine ⟨hψ, fun hhalf => ?_⟩
  obtain ⟨n, hn⟩ := hintegral _ hhalf
  have hn' : (2 : ℝ) * (n : ℝ) = 1 := by
    change (2 : ℝ)⁻¹ * ψ x₀ = (n : ℝ) at hn
    rw [hvalue] at hn
    linarith
  have hn'' : (2 : ℤ) * n = 1 := by exact_mod_cast hn'
  omega

/-- The integer-constant model has an indivisible lift of every full
derivative, including linear forms whose halves also belong to the model. -/
theorem HasIntegralConstantDescription.hasIndivisibleDerivativeLifts
    {x₀ : A} (hΨ : HasIntegralConstantDescription Ψ Φ x₀) :
    HasIndivisibleDerivativeLifts Ψ := by
  intro a
  obtain ⟨η, hη, hηlin⟩ := a.property
  have ha : a.val ∈ Φ := hηlin ▸ ((hΨ η).mp hη).1
  let ψ : A →ᵃ[ℝ] ℝ :=
    AffineMap.mk' (fun x => a.val (x -ᵥ x₀) + 1) a.val x₀ (fun x => by simp)
  have hlin : ψ.linear = a.val := rfl
  have hvalue : ψ x₀ = 1 := by simp [ψ]
  have hψ : ψ ∈ Ψ := (hΨ ψ).mpr ⟨hlin ▸ ha, 1, by simpa using hvalue⟩
  exact ⟨ψ, mem_nonDivisibleRoots_of_apply_eq_one x₀
    (fun η hη => ((hΨ η).mp hη).2) hψ hvalue, hlin⟩

/-- If affine-root membership is detected by pullback, indivisible derivative
lifts descend. The chosen source lift descends because its linear part does.
No surjectivity of the affine map is needed for this implication. -/
theorem HasIndivisibleDerivativeLifts.of_comp
    {Ψ' : Set (B →ᵃ[ℝ] ℝ)} (π : A →ᵃ[ℝ] B)
    (hmem : ∀ ψ' : B →ᵃ[ℝ] ℝ, ψ' ∈ Ψ' ↔ ψ'.comp π ∈ Ψ)
    (hΨ : HasIndivisibleDerivativeLifts Ψ) :
    HasIndivisibleDerivativeLifts Ψ' := by
  rintro ⟨a, η, hη, hηlin⟩
  have ha : a.comp π.linear ∈ derivativeRoots Ψ :=
    ⟨η.comp π, (hmem η).mp hη, by
      change η.linear.comp π.linear = a.comp π.linear
      rw [show η.linear = a from hηlin]⟩
  obtain ⟨ψ, hψ, hψlin⟩ := hΨ ⟨a.comp π.linear, ha⟩
  obtain ⟨ψ', hψ'lin, hcomp⟩ := exists_comp_eq_of_linear_eq π hψlin
  refine ⟨ψ', ⟨(hmem ψ').mpr (hcomp.symm ▸ hψ.1), ?_⟩, hψ'lin⟩
  intro hhalf
  apply hψ.2
  have h := (hmem ((2 : ℝ)⁻¹ • ψ')).mp hhalf
  rwa [smul_comp', hcomp] at h

/-- Changing affine coordinates preserves the full indivisible-lift property. -/
theorem HasIndivisibleDerivativeLifts.transport
    (hΨ : HasIndivisibleDerivativeLifts Ψ) (e : A ≃ᵃ[ℝ] B) :
    HasIndivisibleDerivativeLifts (transportedRoots e Ψ) := by
  apply hΨ.of_comp (e : A →ᵃ[ℝ] B)
  intro ψ
  change ψ ∈ affineFunctionalTransport e '' Ψ ↔ affineFunctionalTransport e.symm ψ ∈ Ψ
  constructor
  · rintro ⟨η, hη, rfl⟩
    simpa only [affineFunctionalTransport_symm_apply] using hη
  · intro hψ
    refine ⟨affineFunctionalTransport e.symm ψ, hψ, ?_⟩
    ext y
    change ψ (e (e.symm y)) = ψ y
    rw [AffineEquiv.apply_symm_apply]

end Langlands.Geometry.Building.AffineRootSystem
