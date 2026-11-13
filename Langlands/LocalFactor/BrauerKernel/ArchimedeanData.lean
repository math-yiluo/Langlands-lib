import Langlands.LocalFactor.BrauerKernel.ArchimedeanTrace
import Langlands.LocalFactor.BrauerKernel.ArchimedeanCount
import Langlands.Global.HeckeNormPower
import Langlands.Global.Factors.HeckeArchimedeanComponents

/-! # Archimedean data of Hecke characters with norm-power archimedean components -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.HeckeFunctionalEquation
open scoped NNReal

section Character

variable {M : Type u} [Field M] [NumberField M]

/-- At a real place, the archimedean component of `‖·‖^t`, read on `ℝ`, is `x ↦ exp(t log |x|)`. -/
theorem realCompletionCharacter_normPower_apply (t : ℂ) {v : NumberField.InfinitePlace M}
    (hv : v.IsReal) (x : ℝˣ) :
    ((realCompletionCharacter hv ((HeckeCharacter.normPower M t).infiniteComponent v) x : ℂˣ) :
      ℂ) = Complex.exp (t * (Real.log |(x : ℝ)| : ℂ)) := by
  change ((HeckeCharacter.normPower M t) (infiniteClassInclusion M v
    (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x)) : ℂ) = _
  rw [HeckeCharacter.normPower_apply, IdeleAbsoluteValue.coe_ideleClass_infiniteClassInclusion]
  have hmult : v.mult = 1 := InfinitePlace.mult_isReal ⟨v, hv⟩
  have hnorm : ‖((Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom
      x : (InfiniteCompletion M v)ˣ) : InfiniteCompletion M v)‖ = |(x : ℝ)| := by
    change ‖(InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (x : ℝ)‖ = |(x : ℝ)|
    rw [(InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm), Real.norm_eq_abs]
  rw [hmult, pow_one, hnorm]

/-- The real archimedean components of `‖·‖^t` agree for all real places of all number fields. -/
theorem realCompletionCharacter_normPower_eq (t : ℂ) {N : Type u} [Field N] [NumberField N]
    {v : NumberField.InfinitePlace M} (hv : v.IsReal) {w : NumberField.InfinitePlace N}
    (hw : w.IsReal) :
    realCompletionCharacter hv ((HeckeCharacter.normPower M t).infiniteComponent v) =
      realCompletionCharacter hw ((HeckeCharacter.normPower N t).infiniteComponent w) := by
  refine DFunLike.ext _ _ fun x => Units.ext ?_
  rw [realCompletionCharacter_normPower_apply, realCompletionCharacter_normPower_apply]

/-- If `Λ` has the archimedean components of `‖·‖^t`, then `Λ⁻¹` has those of `‖·‖^{-t}`, read on
`ℝ` at real places. -/
theorem realCompletionCharacter_inv_eq (t : ℂ) {N : Type u} [Field N] [NumberField N]
    (Λ : HeckeCharacter M) {v : NumberField.InfinitePlace M} (hv : v.IsReal)
    (hΛ : Λ.infiniteComponent v = (HeckeCharacter.normPower M t).infiniteComponent v)
    {w : NumberField.InfinitePlace N} (hw : w.IsReal) :
    realCompletionCharacter hv (Λ⁻¹.infiniteComponent v) =
      realCompletionCharacter hw ((HeckeCharacter.normPower N (-t)).infiniteComponent w) := by
  refine DFunLike.ext _ _ fun x => Units.ext ?_
  rw [realCompletionCharacter_normPower_apply, HeckeCharacter.infiniteComponent_inv]
  have h := realCompletionCharacter_normPower_apply t hv x
  rw [← hΛ] at h
  change (((realCompletionCharacter hv (Λ.infiniteComponent v) x)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val, h, ← Complex.exp_neg, neg_mul]

end Character

section Data

open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open LocalFactor.Archimedean
open scoped Classical

variable {k M : Type u} [Field k] [Field M] [NumberField k] [NumberField M] [Algebra k M]
  [IsTotallyReal M]
  (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles k)) (hψ : ∀ x : k, ψ (diagonal k x) = 1)
  (a : {r : NumberField.InfinitePlace k // r.IsReal} → ℝˣ)
  (ha : ∀ r, IsRealAdditiveComponent ψ r.1 r.2 (a r))

/-- The polar data of `|·|^t` at a real place of the base field. -/
def baseRealData (t : ℂ) (r : {r : NumberField.InfinitePlace k // r.IsReal}) : RealCharacterData :=
  realCharacterData (realCompletionCharacter r.2
    ((HeckeCharacter.normPower k t).infiniteComponent r.1))

omit [NumberField M] [IsTotallyReal M] in
theorem not_isComplex_of_isTotallyReal [IsTotallyReal M] (v : NumberField.InfinitePlace M) :
    ¬ v.IsComplex :=
  InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal v)

/-- **Archimedean data for characters with norm-power archimedean components.** For a totally
real extension `M` of `k`, a Hecke character `Λ` of `M` whose archimedean components are those of
`‖·‖^t`, and the additive character `ψ ∘ Tr` of `A_M`, the archimedean data of the Hecke
functional equation can be taken with the real components `a` of `ψ` and the polar data of
`|·|^{±t}` at the places of `k` below. -/
def normPowerArchData (t : ℂ) (Λ : HeckeCharacter M)
    (hΛ : ∀ v, Λ.infiniteComponent v = (HeckeCharacter.normPower M t).infiniteComponent v) :
    HeckeArchData Λ (traceAdditiveCharacter (L := M) ψ hψ) where
  aR u := a (realComap u)
  haR u := by
    have : u.1.LiesOver (realComap (k := k) u).1 := ⟨rfl⟩
    exact isRealAdditiveComponent_traceAdditiveCharacter ψ hψ (realComap u).1 u.1
      (realComap u).2 u.2 (a _) (ha _)
  aC u := 1
  haC u := absurd u.2 (not_isComplex_of_isTotallyReal u.1)
  dR u := baseRealData t (realComap u)
  dR' u := baseRealData (-t) (realComap u)
  hdR u := by
    rw [hΛ u.1]
    change IsRealCharacterPresentation u.2 _ (realCharacterData (realCompletionCharacter
      (realComap (k := k) u).2 ((HeckeCharacter.normPower k t).infiniteComponent _)))
    rw [← realCompletionCharacter_normPower_eq t u.2 (realComap (k := k) u).2]
    exact isRealCharacterPresentation_realCompletionCharacterData u.2 _
  hdR' u := by
    change IsRealCharacterPresentation u.2 _ (realCharacterData (realCompletionCharacter
      (realComap (k := k) u).2 ((HeckeCharacter.normPower k (-t)).infiniteComponent _)))
    rw [← realCompletionCharacter_inv_eq t Λ u.2 (hΛ u.1) (realComap (k := k) u).2]
    exact isRealCharacterPresentation_realCompletionCharacterData u.2 _
  dC u := absurd u.2 (not_isComplex_of_isTotallyReal u.1)
  dC' u := absurd u.2 (not_isComplex_of_isTotallyReal u.1)
  hdC u := absurd u.2 (not_isComplex_of_isTotallyReal u.1)
  hdC' u := absurd u.2 (not_isComplex_of_isTotallyReal u.1)

/-- The real epsilon factor of `|·|^t` at a real place `r` of the base field, for the real component
`a r` of `ψ`, as a unit. -/
def baseRealEpsilon (t : ℂ) (r : {r : NumberField.InfinitePlace k // r.IsReal}) (s : ℂ) : ℂˣ :=
  (baseRealData t r).epsilon (a r) (NNReal.sqrt ‖((a r : ℝ))‖₊)
    (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (a r).ne_zero)) s

theorem prod_isComplex_eq_one {G : Type*} [CommMonoid G]
    (f : {v : NumberField.InfinitePlace M // v.IsComplex} → G) : ∏ v, f v = 1 := by
  have : IsEmpty {v : NumberField.InfinitePlace M // v.IsComplex} :=
    ⟨fun v => not_isComplex_of_isTotallyReal v.1 v.2⟩
  exact Finset.prod_of_isEmpty _

/-- The archimedean L-function of the data: the `[M : k]`-th power of the product over the real
places of `k` of the reciprocal denominators of `|·|^t`. -/
theorem normPowerArchData_A (t : ℂ) (Λ : HeckeCharacter M)
    (hΛ : ∀ v, Λ.infiniteComponent v = (HeckeCharacter.normPower M t).infiniteComponent v)
    (s : ℂ) :
    (normPowerArchData ψ hψ a ha t Λ hΛ).A s =
      (∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
        ((baseRealData t r).lFactor.denominator s) ^ Module.finrank k M)⁻¹ := by
  unfold HeckeArchData.A heckeInfiniteDenominator
  rw [prod_isComplex_eq_one, mul_one]
  congr 1
  exact prod_realComap (fun r => (baseRealData t r).lFactor.denominator s)

/-- The dual archimedean L-function of the data, with `-t` in place of `t`. -/
theorem normPowerArchData_Ad (t : ℂ) (Λ : HeckeCharacter M)
    (hΛ : ∀ v, Λ.infiniteComponent v = (HeckeCharacter.normPower M t).infiniteComponent v)
    (s : ℂ) :
    (normPowerArchData ψ hψ a ha t Λ hΛ).Ad s =
      (∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
        ((baseRealData (-t) r).lFactor.denominator s) ^ Module.finrank k M)⁻¹ := by
  unfold HeckeArchData.Ad heckeInfiniteDenominator
  rw [prod_isComplex_eq_one, mul_one]
  congr 1
  exact prod_realComap (fun r => (baseRealData (-t) r).lFactor.denominator s)

/-- The archimedean epsilon factor of the data. -/
theorem normPowerArchData_Ae (t : ℂ) (Λ : HeckeCharacter M)
    (hΛ : ∀ v, Λ.infiniteComponent v = (HeckeCharacter.normPower M t).infiniteComponent v)
    (s : ℂ) :
    (normPowerArchData ψ hψ a ha t Λ hΛ).Ae s =
      ((∏ r, (baseRealEpsilon a t r s) ^ Module.finrank k M : ℂˣ) : ℂ) := by
  unfold HeckeArchData.Ae heckeInfiniteEpsilon
  rw [prod_isComplex_eq_one, mul_one, Units.coe_prod]
  simp only [Units.val_pow_eq_pow_val]
  exact prod_realComap (fun r => ((baseRealEpsilon a t r s : ℂˣ) : ℂ))

end Data

section Cancel

open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open LocalFactor.Archimedean
open scoped Classical

variable {k : Type u} [Field k] [NumberField k]

/-- **Cancellation of archimedean L-functions.** If the weighted type counts vanish, the product
over `i` of the quotients of the archimedean L-functions of `|·|^{t₁ i}` and `|·|^{t₂ i}`, each
raised to the `N i`-th power over the real places of `k`, has the punctured germ of `1`. -/
theorem meromorphicEq_prod_baseRealDenominator {ι : Type*} (S : Finset ι) (e : ι → ℤ)
    (N : ι → ℕ) (t₁ t₂ : ι → ℂ)
    (hdim : ∀ τ, ∑ g ∈ S, e g * N g * ((if t₁ g = τ then 1 else 0) -
      (if t₂ g = τ then 1 else 0)) = 0) :
    MeromorphicEq (fun s => ∏ i ∈ S,
      ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
          ((baseRealData (t₁ i) r).lFactor.denominator s) ^ N i)⁻¹ *
        ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
          ((baseRealData (t₂ i) r).lFactor.denominator s) ^ N i)⁻¹)⁻¹) ^ e i) (fun _ => 1) := by
  apply meromorphicEq_of_codiscrete
  let T : Finset ℂ := S.image t₁ ∪ S.image t₂
  have hev : ∀ᶠ s in Filter.codiscrete ℂ, ∀ τ ∈ T,
      ∀ r : {r : NumberField.InfinitePlace k // r.IsReal},
        (baseRealData τ r).lFactor.denominator s ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro τ _
    rw [Filter.eventually_all]
    intro r
    have h := nonzeroMeromorphic_denominator (baseRealData τ r).lFactor
    exact MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero (U := Set.univ) h.1.meromorphicOn
      (fun z _ => h.2 z)
  filter_upwards [hev] with s hs
  let U : ℂ → {r : NumberField.InfinitePlace k // r.IsReal} → ℂˣ := fun τ r =>
    if h : (baseRealData τ r).lFactor.denominator s = 0 then 1 else Units.mk0 _ h
  have hU : ∀ τ ∈ T, ∀ r, ((U τ r : ℂˣ) : ℂ) = (baseRealData τ r).lFactor.denominator s := by
    intro τ hτ r
    simp [U, hs τ hτ r]
  have key : ∀ τ ∈ T, ∀ n : ℕ,
      (∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
        ((baseRealData τ r).lFactor.denominator s) ^ n) = ((∏ r, U τ r ^ n : ℂˣ) : ℂ) := by
    intro τ hτ n
    rw [Units.coe_prod]
    exact Finset.prod_congr rfl fun r _ => by rw [Units.val_pow_eq_pow_val, hU τ hτ r]
  have h1 : ∀ i ∈ S, t₁ i ∈ T := fun i hi => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
  have h2 : ∀ i ∈ S, t₂ i ∈ T := fun i hi => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
  have hcast : ∏ i ∈ S,
      ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
          ((baseRealData (t₁ i) r).lFactor.denominator s) ^ N i)⁻¹ *
        ((∏ r : {r : NumberField.InfinitePlace k // r.IsReal},
          ((baseRealData (t₂ i) r).lFactor.denominator s) ^ N i)⁻¹)⁻¹) ^ e i =
      ((∏ i ∈ S, ((∏ r, U (t₁ i) r ^ N i) * (∏ r, U (t₂ i) r ^ N i)⁻¹) ^ (-e i) : ℂˣ) : ℂ) := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [key _ (h1 i hi), key _ (h2 i hi), Units.val_zpow_eq_zpow_val, Units.val_mul,
      Units.val_inv_eq_inv_val, inv_inv, zpow_neg, ← inv_zpow, mul_inv_rev, inv_inv, mul_comm]
  change _ = (1 : ℂ)
  rw [hcast, prod_types_pow_eq_one S (fun i => -e i) N t₁ t₂ U (fun τ => by
    have h := hdim τ
    simp only [neg_mul, Finset.sum_neg_distrib, h, neg_zero]), Units.val_one]

/-- **Cancellation of archimedean epsilon factors.** Under the same hypothesis, the product of the
quotients of the archimedean epsilon factors is `1` at every point. -/
theorem prod_baseRealEpsilon_eq_one
    (a : {r : NumberField.InfinitePlace k // r.IsReal} → ℝˣ) {ι : Type*} (S : Finset ι)
    (e : ι → ℤ) (N : ι → ℕ) (t₁ t₂ : ι → ℂ)
    (hdim : ∀ τ, ∑ g ∈ S, e g * N g * ((if t₁ g = τ then 1 else 0) -
      (if t₂ g = τ then 1 else 0)) = 0) (s : ℂ) :
    ∏ i ∈ S, (((∏ r, (baseRealEpsilon a (t₁ i) r s) ^ N i : ℂˣ) : ℂ) *
      (((∏ r, (baseRealEpsilon a (t₂ i) r s) ^ N i : ℂˣ) : ℂ))⁻¹) ^ e i = 1 := by
  have hcast : ∏ i ∈ S, (((∏ r, (baseRealEpsilon a (t₁ i) r s) ^ N i : ℂˣ) : ℂ) *
      (((∏ r, (baseRealEpsilon a (t₂ i) r s) ^ N i : ℂˣ) : ℂ))⁻¹) ^ e i =
      ((∏ i ∈ S, ((∏ r, (baseRealEpsilon a (t₁ i) r s) ^ N i) *
        (∏ r, (baseRealEpsilon a (t₂ i) r s) ^ N i)⁻¹) ^ e i : ℂˣ) : ℂ) := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hcast, prod_types_pow_eq_one S e N t₁ t₂ (fun τ r => baseRealEpsilon a τ r s) hdim,
    Units.val_one]

end Cancel

end Langlands.LocalFactor.NonabelianBrauer
