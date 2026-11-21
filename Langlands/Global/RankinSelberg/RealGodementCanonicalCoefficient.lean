import Langlands.Global.RankinSelberg.RealGodementSpectralContinuation

/-! # The canonical continued real Jacquet map on K-finite sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PrincipalSeriesExtension RealGodementProfiles

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "P" => (Fin (r + 1) → ℂ)
local notation "L" => (Fin (r + 1) → Fin 2)
local notation "Y" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "V(" p "," z ")" => Automorphic.realStandardKFinite (r + 1) (characterList p z)
local notation "S(" p "," z ")" => principalSeries ℝ (r + 1) (realPositionCharacter (characterList p z))
local notation "Dᵣ" => RealLocalWhittaker.iteratedRightDerivative r

/-- The continued Jacquet function attached to a fixed K-finite real compact profile. -/
def canonicalJacquetFamily (a : ℝˣ) {p : L} {φ : U → ℂ} (hφ : IsCompactProfile p φ) :
    P → G → ℂ :=
  (realGodementSpectralContinuation r a p φ hφ).choose

theorem canonicalJacquetFamily_properties (a : ℝˣ) {p : L} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) :
    let W := canonicalJacquetFamily a hφ
    (∀ z Xs, Dᵣ Xs (W z) ∈ RealLocalWhittaker.regularFunctions r (-a)) ∧
      HasLocallyUniformDerivativeGrowth Set.univ W ∧
      (∀ Xs g, Differentiable ℂ (fun z => Dᵣ Xs (W z) g)) ∧
      ∀ z ∈ realSpectralChamber r, ∀ g, W z g = additiveJacquetIntegral a (standardSection z φ) g :=
  (realGodementSpectralContinuation r a p φ hφ).choose_spec

theorem canonicalJacquetFamily_agrees (a : ℝˣ) {p : L} {φ : U → ℂ} (hφ : IsCompactProfile p φ)
    {z : P} (hz : z ∈ realSpectralChamber r) :
    canonicalJacquetFamily a hφ z = additiveJacquetIntegral a (standardSection z φ) :=
  funext ((canonicalJacquetFamily_properties a hφ).2.2.2 z hz)

private def chamberJacquetLinear (a : ℝˣ) (p : L) {z : P} (hz : z ∈ realSpectralChamber r) :
    S(p,z) →ₗ[ℂ] (G → ℂ) :=
  additiveJacquetLinear a (RealStrictCharacterLanglandsQuotient.isSignedPower _)
    (isStrictlyDominant_characterList p hz)

private theorem canonicalJacquetFamily_add (a : ℝˣ) {p : L} {φ ψ : U → ℂ}
    (hφ : IsCompactProfile p φ) (hψ : IsCompactProfile p ψ) (hSum : IsCompactProfile p (φ + ψ)) :
    canonicalJacquetFamily a hSum = fun z => canonicalJacquetFamily a hφ z + canonicalJacquetFamily a hψ z := by
  apply eq_of_eqOn_realSpectralChamber ((canonicalJacquetFamily_properties a hSum).2.2.1 [])
    (fun g => ((canonicalJacquetFamily_properties a hφ).2.2.1 [] g).add
      ((canonicalJacquetFamily_properties a hψ).2.2.1 [] g))
  intro z hz g
  simp only [canonicalJacquetFamily_agrees a hSum hz, canonicalJacquetFamily_agrees a hφ hz,
    canonicalJacquetFamily_agrees a hψ hz, Pi.add_apply]
  let f : S(p,z) := ⟨standardSection z φ, (standardSection_mem hφ z).1.1⟩
  let f' : S(p,z) := ⟨standardSection z ψ, (standardSection_mem hψ z).1.1⟩
  let s : S(p,z) := ⟨standardSection z (φ + ψ), (standardSection_mem hSum z).1.1⟩
  have he : s = f + f' := Subtype.ext ((extensionLinear _).map_add φ ψ)
  let J := chamberJacquetLinear a p hz
  change J s g = J f g + J f' g
  rw [he, map_add, Pi.add_apply]

private theorem canonicalJacquetFamily_smul (a : ℝˣ) {p : L} {φ : U → ℂ} (c : ℂ)
    (hφ : IsCompactProfile p φ) (hScale : IsCompactProfile p (c • φ)) :
    canonicalJacquetFamily a hScale = fun z => c • canonicalJacquetFamily a hφ z := by
  apply eq_of_eqOn_realSpectralChamber ((canonicalJacquetFamily_properties a hScale).2.2.1 [])
    (fun g => ((canonicalJacquetFamily_properties a hφ).2.2.1 [] g).const_mul c)
  intro z hz g
  simp only [canonicalJacquetFamily_agrees a hScale hz, canonicalJacquetFamily_agrees a hφ hz]
  let f : S(p,z) := ⟨standardSection z φ, (standardSection_mem hφ z).1.1⟩
  let s : S(p,z) := ⟨standardSection z (c • φ), (standardSection_mem hScale z).1.1⟩
  have he : s = c • f := Subtype.ext ((extensionLinear _).map_smul c φ)
  let J := chamberJacquetLinear a p hz
  change J s g = c * J f g
  rw [he, map_smul, Pi.smul_apply, smul_eq_mul]

/-- At every exponent vector the canonical Jacquet values form a linear map on the
actual K-finite standard source of the corresponding list of characters. -/
def canonicalJacquetMap (a : ℝˣ) (p : L) (z : P) : V(p,z) →ₗ[ℂ] (G → ℂ) where
  toFun f := canonicalJacquetFamily a (isCompactProfile_compactRestriction f.property) z
  map_add' f f' := congrFun (canonicalJacquetFamily_add a (isCompactProfile_compactRestriction f.property)
    (isCompactProfile_compactRestriction f'.property) (isCompactProfile_compactRestriction (f + f').property)) z
  map_smul' c f := congrFun (canonicalJacquetFamily_smul a c (isCompactProfile_compactRestriction f.property)
    (isCompactProfile_compactRestriction (c • f).property)) z

theorem canonicalJacquetMap_standardSection (a : ℝˣ) {p : L} {φ : U → ℂ} (hφ : IsCompactProfile p φ)
    (z : P) :
    canonicalJacquetMap a p z ⟨standardSection z φ, standardSection_mem hφ z⟩ =
      canonicalJacquetFamily a hφ z := by
  have he := compactRestriction_standardSection φ z
  have hCongr {φ ψ : U → ℂ} (hφ : IsCompactProfile p φ) (hψ : IsCompactProfile p ψ)
      (h : φ = ψ) : canonicalJacquetFamily a hφ z = canonicalJacquetFamily a hψ z := by
    cases h
    rfl
  exact hCongr (isCompactProfile_compactRestriction (standardSection_mem hφ z)) hφ he

theorem canonicalJacquetMap_agrees (a : ℝˣ) (p : L) {z : P} (hz : z ∈ realSpectralChamber r) (f : V(p,z)) :
    canonicalJacquetMap a p z f = additiveJacquetIntegral a f.val := by
  change canonicalJacquetFamily a (isCompactProfile_compactRestriction f.property) z = _
  rw [canonicalJacquetFamily_agrees a _ hz, standardSection_compactRestriction f.property]

theorem canonicalJacquetMap_derivative_mem_regularFunctions (a : ℝˣ) (p : L) (z : P)
    (f : V(p,z)) (Xs : List Y) :
    Dᵣ Xs (canonicalJacquetMap a p z f) ∈ RealLocalWhittaker.regularFunctions r (-a) :=
  (canonicalJacquetFamily_properties a (isCompactProfile_compactRestriction f.property)).1 z Xs

/-- The canonical linear maps agree with the convergent integral and send fixed profiles
to the regular, locally uniformly bounded spectral Jacquet families. -/
def RealGodementCanonicalCoefficientStatement (r : ℕ) : Prop :=
  ∀ (a : ℝˣ) (p : Fin (r + 1) → Fin 2),
    (∀ z ∈ realSpectralChamber r, ∀ f, canonicalJacquetMap a p z f = additiveJacquetIntegral a f.val) ∧
    ∀ (φ : Matrix.unitaryGroup (Fin (r + 1)) ℝ → ℂ) (hφ : IsCompactProfile p φ),
      let W (z : Fin (r + 1) → ℂ) :=
        canonicalJacquetMap a p z ⟨standardSection z φ, standardSection_mem hφ z⟩
      (∀ z Xs, RealLocalWhittaker.iteratedRightDerivative r Xs (W z) ∈ RealLocalWhittaker.regularFunctions r (-a)) ∧
      HasLocallyUniformDerivativeGrowth Set.univ W ∧
      ∀ Xs g, Differentiable ℂ (fun z => RealLocalWhittaker.iteratedRightDerivative r Xs (W z) g)

theorem realGodementCanonicalCoefficient : RealGodementCanonicalCoefficientStatement r := by
  intro a p
  refine ⟨fun _ hz f => canonicalJacquetMap_agrees a p hz f, fun φ hφ => ?_⟩
  simp only [canonicalJacquetMap_standardSection a hφ]
  exact ⟨(canonicalJacquetFamily_properties a hφ).1, (canonicalJacquetFamily_properties a hφ).2.1,
    (canonicalJacquetFamily_properties a hφ).2.2.1⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
