import Langlands.BaseChange.CommonShintaniLiftTrace
import Langlands.BaseChange.SigmaLiftGenericFibreStatement
import Langlands.BaseChange.EllipticTwistRigidity
import Langlands.BaseChange.EllipticNormCriterion
import Langlands.BaseChange.RegularTransfer
import Langlands.BaseChange.CommonShintaniLiftNonvanishing
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport
import Langlands.LocalField.CharZeroPadicRealization

/-! # The generic fibre of a σ-lift from finite elliptic trace separation -/

noncomputable section

universe u v uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory TraceFormula

namespace SigmaLiftGenericFibre

end SigmaLiftGenericFibre

/-- The generic fibre statement `SigmaLiftGenericFibreStatement` (Henniart–Lemaire 2011, II.4.8,
Lemme (2)) as a consequence of finite elliptic trace separation
`EllipticDiscreteTraceSeparationStatement`, for the carriers of the two downstairs
representations and for the carrier of the essentially square-integrable one twice. -/
def SigmaLiftGenericFibreReductionStatement.{u₁, v₁, uV₁, uV'₁, uW₁} : Prop :=
  EllipticDiscreteTraceSeparationStatement.{u₁, u₁, max uV₁ uV'₁, uV'₁} →
  EllipticDiscreteTraceSeparationStatement.{u₁, u₁, uV₁, uV₁} →
  SigmaLiftGenericFibreStatement.{u₁, v₁, uV₁, uV'₁, uW₁}

open SigmaLiftGenericFibre in
/-- Regular transfer, Schur's lemma, the elliptic norm criterion, the vanishing of the characters
of generic non-essentially-square-integrable representations at regular elliptic elements and
twist rigidity on the elliptic norms reduce the generic fibre statement to finite elliptic trace
separation. -/
theorem sigmaLiftGenericFibreReduction :
    SigmaLiftGenericFibreReductionStatement.{u, v, uV, uV', uW} := by
  intro hSep hSep₀ F _ _ _ _ _ E _ _ _ _ _ σ l r hE
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (r + 1)
  have := generalLinear_t2Space_of_finite F E (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
  intro ψ V _ _ V' _ _ W _ _ π hπ π' hπ' τ hτ hπirr hπess hgen hτirr A A' c c' hlift hlift'
  let N : Subgroup Fˣ := (Units.map (Algebra.norm F : E →* F)).range
  obtain ⟨hNopen, hNfin⟩ := hE.normRange_isOpen_finiteIndex
  have : N.FiniteIndex := hNfin
  let _ : MeasurableSpace (GeneralLinear (r + 1) F) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
  let _ : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
  -- Schur: the two intertwiners are proportional.
  obtain ⟨a, ha, hA⟩ := A.exists_smul_toLinearMap A' hτ hτirr
  have hc : c ≠ 0 := hlift.1
  have hc' : c' ≠ 0 := hlift'.1
  set t : ℂ := a * c / c' with ht_def
  have ht : t ≠ 0 := div_ne_zero (mul_ne_zero ha hc) hc'
  -- Proportional characters on the elliptic norms.
  have hprop : ∀ (μ : Measure (GeneralLinear (r + 1) F)) [μ.IsHaarMeasure]
      (f : SchwartzBruhat (GeneralLinear (r + 1) F)), IsEllipticSupported f →
      (∀ g, f g ≠ 0 → GeneralLinear.determinant g ∈ N) →
        Character.distribution μ π' hπ' f = t * Character.distribution μ π hπ f := by
    intro μ _ f hf hdet
    let μE : Measure (GeneralLinear (r + 1) E) := Measure.haar
    have : μE.IsHaarMeasure := by dsimp [μE]; infer_instance
    have hvan : VanishesOffNorms σ l μ (f : GeneralLinear (r + 1) F → ℂ) :=
      vanishesOffNorms_of_isNorm_support hE μ (fun g hg =>
        (ellipticNormCriterion F E σ l (r + 1) hE g (hf g hg)).mpr (hdet g hg))
    obtain ⟨φ, -, hconc⟩ :=
      (regularTransfer F E σ l (r + 1) hE μ μE).2 f hf.isRegularSupported hvan
    have h1 := hlift.2 μ μE φ f hconc
    have h2 := hlift'.2 μ μE φ f hconc
    rw [hA, twistedDistribution_smul, LinearMap.smul_apply, h1, smul_eq_mul] at h2
    rw [ht_def]
    field_simp
    linear_combination -h2
  let μ₀ : Measure (GeneralLinear (r + 1) F) := Measure.haar
  have : μ₀.IsHaarMeasure := by dsimp [μ₀]; infer_instance
  -- The generic action is essentially square-integrable.
  have hess' : IsEssentiallySquareIntegrable π' := by
    by_contra hnot
    have hnotp : ¬ (CharZeroLocalField.topologicalData F).IsEssentiallySquareIntegrable π' :=
      fun h => hnot ((isEssentiallySquareIntegrable_iff_padic
        (CharZeroLocalField.topologicalData F) π').mpr h)
    have hvan : ∀ g : GeneralLinear (r + 1) F, IsRegularElliptic g →
        HasCharacterValue π' hπ' g 0 := fun g hg =>
      padicGenericEllipticCharacterVanishing (CharZeroLocalField.residueChar F)
        (CharZeroLocalField.padicField F) (CharZeroLocalField.topologicalData F) r ψ V' π'
        hgen hnotp g hg
    have hzero : ∀ f : SchwartzBruhat (GeneralLinear (r + 1) F), IsEllipticSupported f →
        (∀ g, f g ≠ 0 → GeneralLinear.determinant g ∈ N) →
          Character.distribution μ₀ π hπ f = 0 * Character.distribution μ₀ π hπ f := by
      intro f hf hdet
      have h' : Character.distribution μ₀ π' hπ' f = 0 :=
        distribution_eq_zero_of_localValues_zero fun x hx => hvan x (hf x hx) μ₀
      have h := hprop μ₀ f hf hdet
      rw [h'] at h
      rw [zero_mul]
      exact (mul_eq_zero.mp h.symm).resolve_left ht
    exact (ellipticTwistRigidity_of_separation hSep₀ F (r + 1) (Nat.succ_pos r) N hNopen μ₀
      π hπ π hπ hπirr hπirr hπess hπess 0 hzero).1 rfl
  -- Twist rigidity on the elliptic norms.
  obtain ⟨-, κ, hκ, he⟩ := ellipticTwistRigidity_of_separation hSep F (r + 1) (Nat.succ_pos r)
    N hNopen μ₀ π hπ π' hπ' hπirr hgen.1 hπess hess' t (hprop μ₀)
  exact ⟨κ, fun x => hκ _ ⟨x, rfl⟩, he⟩

end Langlands.BaseChange
