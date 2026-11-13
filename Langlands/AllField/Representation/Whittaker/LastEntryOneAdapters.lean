import Langlands.Representation.Whittaker.LastEntryOneAdapters
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Group.GL.UnramifiedCharacter
import Langlands.AllField.HarmonicAnalysis.Conductor
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.AllField.Representation.Whittaker.LastEntryOneAssembly
import Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportStatement
/-!
# Coefficient and support adapters for the last-entry-one expansion

The upper-support adapter explicitly assumes the published support proposition.
These helpers do not establish the analytic expansion.
-/

noncomputable section

namespace Langlands.AllField.WhittakerLastEntryOne
open Langlands.WhittakerLastEntryOne hiding assemble continuous_rootLiftHom pullback_injective rootCoefficientMap rootCoefficientMap_apply rootCoefficientSpace rootCoefficientSpace_locallyConstant rootCoefficientSpace_upper_support rootHom_rootLift rootLiftHom rootLift_last rootLift_rootHom upper_support_of_statement
open Langlands.AllField.WhittakerLastEntryOne

open scoped BigOperators

universe uF uV uG

section RootCoefficientSpace

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ)

/-- The cumulative-product section as an actual group homomorphism. -/
def rootLiftHom : (Fin n → Fˣ) →* (Fin (n + 1) → Fˣ) where
  toFun := rootLift
  map_one' := by
    have h := rootLift_rootHom F T n 1 rfl
    rw [map_one] at h
    exact h
  map_mul' x y := by
    have h := rootLift_rootHom F T n (rootLift x * rootLift y) (by
      change rootLift x (Fin.last n) * rootLift y (Fin.last n) = 1
      rw [rootLift_last F T n, rootLift_last F T n, one_mul])
    rw [map_mul, rootHom_rootLift F T n, rootHom_rootLift F T n] at h
    exact h

theorem continuous_rootLiftHom :
    letI := T.topology
    Continuous (rootLiftHom F T n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply (Langlands.AllField.RankinSelberg.rootCoordinateChange F T n).1.comp
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin n → Fˣ => (1 : Fˣ)))
  | cast i => simpa only [Fin.lastCases_castSucc] using
      (continuous_apply i : Continuous (fun x : Fin n → Fˣ => x i))

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)

/-- Restriction of an actual matrix coefficient to the simple-root torus,
with its intertwining law for right translation. -/
def rootCoefficientMap :
    Representation.IntertwiningMap (ρ.comp (torus.comp (rootLiftHom F T n)))
      (Whittaker.rightTranslation ℂ (Fin n → Fˣ)) where
  toLinearMap := matrixCoefficient (ρ.comp (torus.comp (rootLiftHom F T n))) ℓ
  isIntertwining' x := by
    ext v y
    change ℓ ((ρ.comp (torus.comp (rootLiftHom F T n))) y
        ((ρ.comp (torus.comp (rootLiftHom F T n))) x v)) =
      ℓ ((ρ.comp (torus.comp (rootLiftHom F T n))) (y * x) v)
    rw [map_mul, Module.End.mul_apply]

/-- The actual translation-stable space of root-coordinate coefficients. -/
def rootCoefficientSpace :
    Subrepresentation (Whittaker.rightTranslation ℂ (Fin n → Fˣ)) :=
  (rootCoefficientMap F T n V ρ ℓ).range

@[simp]
theorem rootCoefficientMap_apply (v : V) (x : Fin n → Fˣ) :
    rootCoefficientMap F T n V ρ ℓ v x =
      ℓ (ρ (torus (rootLift x)) v) := rfl

/-- Every function in the actual coefficient image is locally constant.
This uses smoothness of the orbit map, without any topology on the carrier. -/
theorem rootCoefficientSpace_locallyConstant :
    letI := T.topology
    IsSmooth ρ →
      ∀ f : (rootCoefficientSpace F T n V ρ ℓ).toSubmodule,
        IsLocallyConstant f.val := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ f
  obtain ⟨v, hv⟩ := f.property
  rw [← hv]
  exact (Hecke.orbitMap_locallyConstant
    (ρ.comp (torus.comp (rootLiftHom F T n)))
    (isSmooth_comp (torus.comp (rootLiftHom F T n))
      (continuous_torus.comp (continuous_rootLiftHom F T n)) hρ v)).comp ℓ

end RootCoefficientSpace

/-- The supplied-topology support proposition implies the raw coefficient bound
needed by the root-coordinate function space, with one bound for every root. -/
theorem upper_support_of_statement
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (hsupport : Langlands.AllField.Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T n) :
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
      (ψ : AddChar F ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ → ∀ ℓ : Module.Dual ℂ V,
      (∀ g : GeneralLinear (n + 1) F,
        ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
        ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) →
      ∀ v : V, ∃ R : ℝ, 0 < R ∧
        ∀ (a : Fin (n + 1) → Fˣ) (i : Fin n),
          R < T.normalizedAbs (roots a i) → ℓ (ρ (torus a) v) = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro V _ _ ρ ψ hc hne hu hρ ℓ hℓ v
  let ψ' := HarmonicAnalysis.UnitaryAdditiveCharacter.ofComplex ψ hc hne hu
  let ℓ' : Whittaker.glFunctionals ψ' n ρ :=
    ⟨ℓ, mem_glFunctionals_of_raw ρ ψ hc hne hu ℓ hℓ⟩
  obtain ⟨R, hR, hbound⟩ :=
    hsupport ψ' V ρ hρ ℓ' (Whittaker.modelMap ρ ℓ' v)
  refine ⟨R, hR, ?_⟩
  intro a i hi
  by_contra hneval
  have hn : (Whittaker.modelMap ρ ℓ' v).val.val
      (GeneralLinear.Iwasawa.diagonalUnits a * 1) ≠ 0 := by
    change ℓ (ρ (GeneralLinear.Iwasawa.diagonalUnits a * 1) v) ≠ 0
    simpa only [mul_one, ← torus_eq_diagonalUnits] using hneval
  exact (not_lt_of_ge (hbound a 1 (Subgroup.one_mem _) hn i)) hi

/-- The support proposition bounds all coordinates of each function in the
actual root coefficient image, uniformly in the other coordinates. -/
theorem rootCoefficientSpace_upper_support
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (hsupport : Langlands.AllField.Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T n) :
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
      (ψ : AddChar F ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ → ∀ ℓ : Module.Dual ℂ V,
      (∀ g : GeneralLinear (n + 1) F,
        ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
        ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) →
      ∀ f : (rootCoefficientSpace F T n V ρ ℓ).toSubmodule,
        ∃ R : ℝ, 0 < R ∧ ∀ (x : Fin n → Fˣ) (i : Fin n),
          R < T.normalizedAbs (x i : F) → f.val x = 0 := by
  let := T.topology
  intro V _ _ ρ ψ hc hne hu hρ ℓ hℓ f
  obtain ⟨v, hv⟩ := f.property
  obtain ⟨R, hR, hbound⟩ :=
    upper_support_of_statement F T n hsupport V ρ ψ hc hne hu hρ ℓ hℓ v
  refine ⟨R, hR, ?_⟩
  intro x i hi
  rw [← hv]
  change ℓ (ρ (torus (rootLift x)) v) = 0
  apply hbound (rootLift x) i
  simpa only [roots, rootHom_rootLift F T n] using hi

end Langlands.AllField.WhittakerLastEntryOne
