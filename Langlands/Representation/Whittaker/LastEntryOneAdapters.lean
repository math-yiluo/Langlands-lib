import Langlands.Representation.Whittaker.LastEntryOneAssembly
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportStatement
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Hecke.ActionIntegrand

/-!
# Coefficient and support adapters for the last-entry-one expansion

The upper-support adapter explicitly assumes the published support proposition.
These helpers do not establish the analytic expansion.
-/

noncomputable section

namespace Langlands.WhittakerLastEntryOne

open scoped BigOperators

universe uF uV uG

theorem torus_eq_diagonalUnits {K : Type uF} [Field K] {n : ℕ}
    (a : Fin (n + 1) → Kˣ) :
    torus a = GeneralLinear.Iwasawa.diagonalUnits a := by
  apply Units.ext
  rfl

theorem continuous_torus {K : Type uF} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} :
    Continuous (torus (K := K) (n := n)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun a : Fin (n + 1) → Kˣ =>
      Matrix.diagonal (fun i => (a i : K)))
    fun_prop
  · change Continuous (fun a : Fin (n + 1) → Kˣ =>
      Matrix.diagonal (fun i => (((a i)⁻¹ : Kˣ) : K)))
    fun_prop

section RootCoefficientSpace

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ)

/-- The cumulative-product section as an actual group homomorphism. -/
def rootLiftHom : (Fin n → F.Carrierˣ) →* (Fin (n + 1) → F.Carrierˣ) where
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
  apply (RankinSelberg.rootCoordinateChange F T n).1.comp
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin n → F.Carrierˣ => (1 : F.Carrierˣ)))
  | cast i => simpa only [Fin.lastCases_castSucc] using
      (continuous_apply i : Continuous (fun x : Fin n → F.Carrierˣ => x i))

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)

/-- Restriction of an actual matrix coefficient to the simple-root torus,
with its intertwining law for right translation. -/
def rootCoefficientMap :
    Representation.IntertwiningMap (ρ.comp (torus.comp (rootLiftHom F T n)))
      (Whittaker.rightTranslation ℂ (Fin n → F.Carrierˣ)) where
  toLinearMap := matrixCoefficient (ρ.comp (torus.comp (rootLiftHom F T n))) ℓ
  isIntertwining' x := by
    ext v y
    change ℓ ((ρ.comp (torus.comp (rootLiftHom F T n))) y
        ((ρ.comp (torus.comp (rootLiftHom F T n))) x v)) =
      ℓ ((ρ.comp (torus.comp (rootLiftHom F T n))) (y * x) v)
    rw [map_mul, Module.End.mul_apply]

/-- The actual translation-stable space of root-coordinate coefficients. -/
def rootCoefficientSpace :
    Subrepresentation (Whittaker.rightTranslation ℂ (Fin n → F.Carrierˣ)) :=
  (rootCoefficientMap F T n V ρ ℓ).range

@[simp]
theorem rootCoefficientMap_apply (v : V) (x : Fin n → F.Carrierˣ) :
    rootCoefficientMap F T n V ρ ℓ v x =
      ℓ (ρ (torus (rootLift x)) v) := rfl

theorem rootCoefficientSpace_smooth :
    letI := T.topology
    IsSmooth ρ →
      IsSmooth (R := ℂ) (G := Fin n → F.Carrierˣ)
        (V := (rootCoefficientSpace F T n V ρ ℓ).toSubmodule)
        (rootCoefficientSpace F T n V ρ ℓ).toRepresentation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ w
  obtain ⟨v, hv⟩ := w.property
  obtain ⟨K, hK⟩ := isSmooth_comp (torus.comp (rootLiftHom F T n))
    (continuous_torus.comp (continuous_rootLiftHom F T n)) hρ v
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  change Whittaker.rightTranslation ℂ (Fin n → F.Carrierˣ) (k : Fin n → F.Carrierˣ)
    w.val = w.val
  rw [← hv]
  change Whittaker.rightTranslation ℂ (Fin n → F.Carrierˣ) (k : Fin n → F.Carrierˣ)
    (rootCoefficientMap F T n V ρ ℓ v) = rootCoefficientMap F T n V ρ ℓ v
  rw [← (rootCoefficientMap F T n V ρ ℓ).isIntertwining]
  exact congrArg (rootCoefficientMap F T n V ρ ℓ) (hK k)

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

/-- Finite generation passes to the actual coefficient image. -/
theorem model_finite
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup G} {θ : N →* ℂˣ}
    (ρ : Representation ℂ G V) (ℓ : Whittaker.functionals N θ ρ)
    (hfinite : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule) :
    Module.Finite (MonoidAlgebra ℂ G) (Whittaker.modelRepresentation ρ ℓ).asModule := by
  let := hfinite
  exact Module.Finite.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (Whittaker.modelMap ρ ℓ))
    (Whittaker.modelMap_surjective ρ ℓ)

/-- Admissibility passes to the coefficient image with the target's canonical topology. -/
theorem model_admissible
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    {N : Subgroup (GeneralLinear (n + 1) F.Carrier)} {θ : N →* ℂˣ}
    (ℓ : Whittaker.functionals N θ ρ) :
    letI := F.canonicalTopologicalData.topology
    IsAdmissible ρ →
      IsAdmissible (R := ℂ) (G := GeneralLinear (n + 1) F.Carrier)
        (V := (Whittaker.coefficientModel ρ ℓ).toSubmodule)
        (Whittaker.modelRepresentation ρ ℓ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro hρ
  exact Unramified.SphericalExistence.isAdmissible_of_surjective
    (Unramified.SphericalExistence.exists_compactOpenSubgroup_le F)
    (Whittaker.modelMap ρ ℓ) (Whittaker.modelMap_surjective ρ ℓ) hρ

/-- The supplied-topology support proposition implies the raw coefficient bound
needed by the root-coordinate function space, with one bound for every root. -/
theorem upper_support_of_statement
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hsupport : Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T n) :
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ → ∀ ℓ : Module.Dual ℂ V,
      (∀ g : GeneralLinear (n + 1) F.Carrier,
        ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
        ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) →
      ∀ v : V, ∃ R : ℝ, 0 < R ∧
        ∀ (a : Fin (n + 1) → F.Carrierˣ) (i : Fin n),
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
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hsupport : Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T n) :
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ → ∀ ℓ : Module.Dual ℂ V,
      (∀ g : GeneralLinear (n + 1) F.Carrier,
        ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
        ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) →
      ∀ f : (rootCoefficientSpace F T n V ρ ℓ).toSubmodule,
        ∃ R : ℝ, 0 < R ∧ ∀ (x : Fin n → F.Carrierˣ) (i : Fin n),
          R < T.normalizedAbs (x i : F.Carrier) → f.val x = 0 := by
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

end Langlands.WhittakerLastEntryOne
