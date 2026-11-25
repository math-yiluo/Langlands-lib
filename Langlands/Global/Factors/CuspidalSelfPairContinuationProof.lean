import Langlands.Global.RankinSelberg.EqualUnfoldingProof
import Langlands.Global.RankinSelberg.SelfPairIntegralPositivity
import Langlands.Global.RankinSelberg.SelfPairSchwartz
import Langlands.Global.RankinSelberg.SelfPairContragredient
import Langlands.Global.RankinSelberg.SelfPairEulerBound
import Langlands.Global.Factors.CuspidalSelfPairContinuationAssembly
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # Self-pair continuation from equal-rank unfolding and positivity -/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Langlands.Global

open Automorphic RankinSelbergGlobal RankinSelbergGlobal.SelfPair
open CuspidalPairBoundaryNonvanishing CuspidalPairFunctionalEquation
open CuspidalPairAbsoluteConvergence
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

local instance selfPairSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance selfPairSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- The standard-outside condition is preserved when the finite exceptional
set is enlarged. -/
private theorem isStandardOutside_mono {n : ℕ} {S A : Finset (FinitePlace F)}
    (hSA : S ⊆ A) {Φ : RowVector F n → ℂ}
    (hΦ : IsStandardOutside F n S Φ) : IsStandardOutside F n A Φ := by
  have hinc : integralOutside F n S ⊆ integralOutside F n A :=
    fun x hx v hv => hx v fun hvS => hv (hSA hvS)
  constructor
  · intro x hx
    exact hΦ.1 x fun h => hx (hinc h)
  · intro x z hx hz harch hloc
    have hxz : x ∈ integralOutside F n S ↔ z ∈ integralOutside F n S := by
      constructor <;> intro h v hv j <;> by_cases hvA : v ∈ A
      · rw [← congrFun (hloc v hvA) j]
        exact h v hv j
      · exact hz v hvA j
      · rw [congrFun (hloc v hvA) j]
        exact h v hv j
      · exact hx v hvA j
    by_cases hxS : x ∈ integralOutside F n S
    · exact hΦ.2 x z hxS (hxz.mp hxS) harch fun v hv => hloc v (hSA hv)
    · rw [hΦ.1 x hxS, hΦ.1 z (mt hxz.mpr hxS)]

variable [CompactSpace (AdeleQuotient F)]

private theorem isSphericalOutside_mono {r : ℕ} {T : CuspidalOperatorRealization F r}
    {S A : Finset (FinitePlace F)} (hSA : S ⊆ A) {x : T.Space}
    (hx : IsSphericalOutside F T S x) : IsSphericalOutside F T A x :=
  fun v hv => hx v fun hvS => hv (hSA hvS)

/-- Jacquet–Shalika I, Lemma (5.2), for actual cuspidal realizations. The partial
self-pair Euler product continues holomorphically to `Re s > 1`. -/
theorem cuspidalSelfPairContinuation : CuspidalSelfPairContinuationStatement.{u, uQ} := by
  classical
  intro K _ _ _ r T Td hT hTd P Pd S hP hPd
  obtain ⟨Pc⟩ := exists_conjugatePresentation T hT P
  have hTc := HasUnitaryCentralCharacter.conjugate hT
  let ψ := HeckeFunctionalEquation.standardGlobalAdditiveCharacter K
  have hψ : ∀ a : K, ψ (algebraMap K (Adeles K) a) = 1 :=
    HeckeFunctionalEquation.standardGlobalAdditiveCharacter_diagonal K
  have hstd : IsStandardAdditiveCharacter K ψ.complex :=
    isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨Sψ, hSψ⟩ := exists_finiteAdditiveSupport ψ hψ
  obtain ⟨x, hx, hxS⟩ := exists_sphericalOutside_ne_zero P hP
  obtain ⟨g, hg⟩ := exists_cuspWhittaker_ne_zero T ψ.complex hstd hx
  obtain ⟨SΦ, Φ, hΦ, hΦS, hΦnonneg, hΦg⟩ :=
    positiveStandardSchwartz K r.succ (lastRow K r g)
  have hTunit := hT
  obtain ⟨ω, hωu, hω⟩ := hTunit
  obtain ⟨I, R, hI, hIR⟩ :=
    exists_holomorphic_equalWhittakerIntegral equalUnfoldingStatement_proof.{u}
      T ω hωu hω ψ.complex hstd x (fun y => (Φ y : ℂ)) hΦ
  let W := cuspWhittaker K T ψ.complex x
  let Wc := cuspWhittaker K T.conjugate ψ.complex⁻¹ (T.conjugateEquiv x)
  let G := equalWhittakerIntegrand K W Wc (fun y => (Φ y : ℂ))
  let f : WhittakerQuotient K (r + 1) → ℝ :=
    fun q => ‖W q.out‖ ^ 2 * Φ (lastRow K r q.out)
  have hG : SelfPairLandau.IsMellin G f := by
    intro s q
    exact equalWhittakerIntegrand_conjugate T ψ.complex ψ.norm_complex x Φ s q
  have hf : ∀ q, 0 ≤ f q :=
    fun q => mul_nonneg (sq_nonneg _) (hΦnonneg _)
  have hint : ∀ s : ℂ, 1 < s.re →
      Integrable (G s) (whittakerQuotientMeasure K (r + 1)) :=
    hG.integrable_of_differentiableOn hf (fun s hs => (hIR s hs).1) hI
      (fun s hs => (hIR s hs).2)
  let B := S ∪ Pc.exceptional ∪ Sψ ∪ SΦ
  have hSB : S ⊆ B := by intro v hv; simp [B, hv]
  have hPcB : Pc.exceptional ⊆ B := by intro v hv; simp [B, hv]
  have hSψB : Sψ ⊆ B := by intro v hv; simp [B, hv]
  have hSΦB : SΦ ⊆ B := by intro v hv; simp [B, hv]
  obtain ⟨A, hBA, hposA⟩ :=
    exists_partialEqualWhittakerIntegral_conjugate_pos T ψ.complex hstd x Φ hΦ hΦnonneg
      g hg (by rw [hΦg]; exact zero_lt_one) 2 (hint 2 (by norm_num)) B
  have hPA : P.exceptional ⊆ A := hP.trans (hSB.trans hBA)
  have hPdA : Pd.exceptional ⊆ A := hPd.trans (hSB.trans hBA)
  have hPcA : Pc.exceptional ⊆ A := hPcB.trans hBA
  have hΦA : IsStandardOutside K (r + 1) A (fun y => (Φ y : ℂ)) :=
    isStandardOutside_mono (hSΦB.trans hBA) hΦS
  have hψA : FunctionalEquationComparison.FiniteAdditiveSupport ψ A :=
    finiteAdditiveSupport_mono hSψ (hSψB.trans hBA)
  have hxA : IsSphericalOutside K T A x := isSphericalOutside_mono (hSB.trans hBA) hxS
  have hxcA : IsSphericalOutside K T.conjugate A (T.conjugateEquiv x) :=
    isSphericalOutside_conjugate hxA
  have hC : HasSatakeBound P (1 / 2 : ℝ) := by
    intro v hv α hα
    simpa only [Real.sqrt_eq_rpow] using norm_eigenvalue_le_sqrt hT P v hv hα
  have hCc : HasSatakeBound Pc (1 / 2 : ℝ) := by
    intro v hv α hα
    simpa only [Real.sqrt_eq_rpow] using norm_eigenvalue_le_sqrt hTc Pc v hv hα
  apply CuspidalSelfPairAssembly.continuation_of_prod_bound_other hT hTd P Pd hP hPd hPA hPdA
  intro σ hσ
  obtain ⟨M, hM⟩ :=
    SelfPairEulerBound.prod_bound_of_re_pos ψ hψ hPA hPcA hψA hC hCc
      (fun v hv α hα => norm_eigenvalue_le_sqrt hT P v (fun h => hv (hPA h)) hα)
      (fun v hv α hα => norm_eigenvalue_le_sqrt hTc Pc v (fun h => hv (hPcA h)) hα)
      hxA hxcA hΦA hG hf hint (σ₀ := 2) (by norm_num) hposA hσ
  refine ⟨M, fun E => ?_⟩
  have heq : (∏ v ∈ E, partialEulerFactor P Pc hPA hPcA v (σ : ℂ)) =
      ∏ v ∈ E, partialEulerFactor P Pd hPA hPdA v (σ : ℂ) :=
    Finset.prod_congr rfl fun v _ =>
      partialEulerFactor_conjugate_eq hT hTd P Pc Pd hPA hPcA hPdA v σ
  rw [← heq]
  exact hM E

end Langlands.Global
