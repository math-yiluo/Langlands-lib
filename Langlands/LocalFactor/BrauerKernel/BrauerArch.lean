import Langlands.LocalFactor.BrauerKernel.ArchimedeanData
import Langlands.Global.Factors.RelativeWeilAssemblyGlobal

/-! # The archimedean block of the Brauer product package -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open scoped Classical

variable {k E : Type u} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [IsTotallyReal E]

/-- An intermediate field of a totally real field is totally real. -/
theorem isTotallyReal_intermediateField (M : IntermediateField k E) : IsTotallyReal M :=
  IsTotallyReal.of_algebra M E

attribute [local instance] isTotallyReal_intermediateField

variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles k))
  (hψ : ∀ x : k, ψ (diagonal k x) = 1)
  (a : {r : NumberField.InfinitePlace k // r.IsReal} → ℝˣ)
  (ha : ∀ r, IsRealAdditiveComponent ψ r.1 r.2 (a r))
  {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField k E) (t₁ t₂ : Fin n → ℂ)
  (Λ₁ Λ₂ : ∀ i, HeckeCharacter (K i))
  (hΛ₁ : ∀ i v, (Λ₁ i).infiniteComponent v =
    (HeckeCharacter.normPower (K i) (t₁ i)).infiniteComponent v)
  (hΛ₂ : ∀ i v, (Λ₂ i).infiniteComponent v =
    (HeckeCharacter.normPower (K i) (t₂ i)).infiniteComponent v)
  (hdim : ∀ τ, ∑ i ∈ Finset.univ, r i * (Module.finrank k (K i) : ℤ) *
    ((if t₁ i = τ then 1 else 0) - (if t₂ i = τ then 1 else 0)) = 0)

include hdim in
/-- The archimedean L-function of the Brauer product package (with exponent `0` on the base
character) has the punctured germ of `1`. -/
theorem meromorphicEq_brauerArch_A {χ : HeckeCharacter k} (DF : HeckeArchData χ ψ) :
    MeromorphicEq (fun s => DF.A s ^ (0 : ℤ) * ∏ i ∈ Finset.univ,
      ((normPowerArchData ψ hψ a ha (t₁ i) (Λ₁ i) (hΛ₁ i)).A s *
        ((normPowerArchData ψ hψ a ha (t₂ i) (Λ₂ i) (hΛ₂ i)).A s)⁻¹) ^ r i) (fun _ => 1) := by
  have h := meromorphicEq_prod_baseRealDenominator (k := k) Finset.univ r
    (fun i => Module.finrank k (K i)) t₁ t₂ hdim
  have heq : (fun s => DF.A s ^ (0 : ℤ) * ∏ i ∈ Finset.univ,
      ((normPowerArchData ψ hψ a ha (t₁ i) (Λ₁ i) (hΛ₁ i)).A s *
        ((normPowerArchData ψ hψ a ha (t₂ i) (Λ₂ i) (hΛ₂ i)).A s)⁻¹) ^ r i) =
      (fun s => ∏ i ∈ Finset.univ,
        ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
            ((baseRealData (t₁ i) r).lFactor.denominator s) ^ Module.finrank k (K i))⁻¹ *
          ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
            ((baseRealData (t₂ i) r).lFactor.denominator s) ^
              Module.finrank k (K i))⁻¹)⁻¹) ^ r i) := by
    funext s
    rw [zpow_zero, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [normPowerArchData_A, normPowerArchData_A]
  rw [heq]
  exact h

include hdim in
/-- The dual archimedean L-function of the Brauer product package has the punctured germ of
`1`. -/
theorem meromorphicEq_brauerArch_Ad {χ : HeckeCharacter k} (DF : HeckeArchData χ ψ) :
    MeromorphicEq (fun s => DF.Ad s ^ (0 : ℤ) * ∏ i ∈ Finset.univ,
      ((normPowerArchData ψ hψ a ha (t₁ i) (Λ₁ i) (hΛ₁ i)).Ad s *
        ((normPowerArchData ψ hψ a ha (t₂ i) (Λ₂ i) (hΛ₂ i)).Ad s)⁻¹) ^ r i) (fun _ => 1) := by
  have hdim' : ∀ τ, ∑ i ∈ Finset.univ, r i * (Module.finrank k (K i) : ℤ) *
      ((if -t₁ i = τ then 1 else 0) - (if -t₂ i = τ then 1 else 0)) = 0 := by
    intro τ
    simp only [neg_eq_iff_eq_neg]
    exact hdim (-τ)
  have h := meromorphicEq_prod_baseRealDenominator (k := k) Finset.univ r
    (fun i => Module.finrank k (K i)) (fun i => -t₁ i) (fun i => -t₂ i) hdim'
  have heq : (fun s => DF.Ad s ^ (0 : ℤ) * ∏ i ∈ Finset.univ,
      ((normPowerArchData ψ hψ a ha (t₁ i) (Λ₁ i) (hΛ₁ i)).Ad s *
        ((normPowerArchData ψ hψ a ha (t₂ i) (Λ₂ i) (hΛ₂ i)).Ad s)⁻¹) ^ r i) =
      (fun s => ∏ i ∈ Finset.univ,
        ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
            ((baseRealData (-t₁ i) r).lFactor.denominator s) ^ Module.finrank k (K i))⁻¹ *
          ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
            ((baseRealData (-t₂ i) r).lFactor.denominator s) ^
              Module.finrank k (K i))⁻¹)⁻¹) ^ r i) := by
    funext s
    rw [zpow_zero, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [normPowerArchData_Ad, normPowerArchData_Ad]
  rw [heq]
  exact h

include hdim in
/-- The archimedean epsilon factor of the Brauer product package is `1`. -/
theorem brauerArch_Ae_eq_one {χ : HeckeCharacter k} (DF : HeckeArchData χ ψ) (s : ℂ) :
    DF.Ae s ^ (0 : ℤ) * ∏ i ∈ Finset.univ,
      ((normPowerArchData ψ hψ a ha (t₁ i) (Λ₁ i) (hΛ₁ i)).Ae s *
        ((normPowerArchData ψ hψ a ha (t₂ i) (Λ₂ i) (hΛ₂ i)).Ae s)⁻¹) ^ r i = 1 := by
  rw [zpow_zero, one_mul]
  refine Eq.trans ?_ (prod_baseRealEpsilon_eq_one a Finset.univ r
    (fun i => Module.finrank k (K i)) t₁ t₂ hdim s)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [normPowerArchData_Ae, normPowerArchData_Ae]

end Langlands.LocalFactor.NonabelianBrauer
