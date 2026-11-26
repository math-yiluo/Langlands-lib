import Langlands.Analysis.Complex.AnalyticFamilyRange
import Langlands.Global.RankinSelberg.ComplexGodementGaussianSpanning
import Langlands.Global.RankinSelberg.ComplexJacquetSchwartzEvaluation
import Langlands.Global.RankinSelberg.ComplexJacquetGeneratorEvaluation
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient

/-! # Continued Schwartz Godement values in the irreducible complex Whittaker model -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extensionLinear)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open ArchimedeanLocal
open ComplexCompactProfileFamily (characterList IsCompactProfile standardSection standardSection_mem
  standardSection_compactRestriction standardSection_unitary compactRestriction compactRestriction_isCompactProfile)
open ComplexGodement (addedCharacter retainedCharacters smallerExponents smallerWeights characterList_cons
  godementSection godementSectionIntegrand translateTest characterWeight complexGodementStandardConvergence
  schwartzSection_standard finiteDimensional_schwartzSection_profiles)
open ComplexGodementAddedCharacter (continuedValue continuedValue_eq_shiftedCharacter)
open ComplexGodementGeneratorFamily (differentiable_generatorValue)
open ComplexJacquetChamberHolomorphic (chamber isOpen_chamber)
open ComplexJacquetContinuation (canonicalJacquetFamily canonicalJacquetFamily_properties continuedJacquet
  continuedJacquetFamilies continuedJacquetFamilies_apply complexJacquetSchwartzEvaluation
  complexJacquetIntertwiner complexJacquetNonzero)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

/-- A nonzero exact Whittaker intertwiner on an irreducible standard module is injective. -/
theorem IsComplexWhittakerIntertwiner.injective_of_irreducible {r : ℕ} {ds : List ComplexCharacterData}
    {a : ℂˣ} {B : complexStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (hB₀ : B ≠ 0)
    (hirr : IsIrreducibleGKModule (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds)) :
    Function.Injective B := by
  have hker : LinearMap.ker B = ⊥ ∨ LinearMap.ker B = ⊤ := by
    apply hirr.2
    · intro k f hf
      rw [LinearMap.mem_ker] at hf ⊢
      let k' : unitaryCompact ℂ (r + 1) := ⟨Unitary.toUnits k, k.2⟩
      rw [hB.2.2.2.1 k' f ((complexStandardRep (r + 1) ds) k f) rfl, hf, map_zero]
    · intro X f hf
      rw [LinearMap.mem_ker] at hf ⊢
      induction X using TensorProduct.inductionOn with
      | tmul z Y =>
          have he : (z ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) =
              z • (1 ⊗ₜ[ℝ] Y) := by simp [TensorProduct.smul_tmul']
          rw [he, map_smul, LinearMap.smul_apply, map_smul]
          have hc : (((complexStandardLie (r + 1) ds) (1 ⊗ₜ[ℝ] Y) f : complexStandardKFinite (r + 1) ds) :
              Langlands.GeneralLinear (r + 1) ℂ → ℂ) =
              rightDerivative (matrixModel ℂ (r + 1)) Y f := by
            rw [complexStandardLie, principalSeriesLie, kFiniteLie_one_tmul_apply_coe]
          rw [hB.2.2.2.2 Y f _ hc, hf, ComplexStrictLanglandsQuotient.rightDerivative_zero, smul_zero]
      | add X Y hX hY =>
          rw [map_add, LinearMap.add_apply, map_add, hX, hY, zero_add]
  rcases hker with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact False.elim (hB₀ (LinearMap.ker_eq_top.mp h))

namespace ComplexGodementContinuedModel

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 1 + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ
local notation "P" => (Fin n → ℂ)
local notation "Q" => (Fin m → ℂ)
local notation "L" => (Fin n → ℤ)
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Std[" l "," p "]" => complexStandardKFinite n (characterList l p)

private theorem headTail_chamber (q : Q) (hq : q ∈ chamber r) (z : ℂ) (hz : (q 0).re < z.re) :
    (Fin.cons z q : P) ∈ chamber (r + 1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz
  · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hq j

private theorem differentiable_adjoin (q : Q) : Differentiable ℂ (fun z : ℂ => (Fin.cons z q : P)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact differentiable_id
  · exact differentiable_const _

private def strongChamber (M : Q → ℕ) : Set P :=
  {p | p ∈ chamber (r + 1) ∧ (m : ℝ) + M (smallerExponents p) ≤ (p 0 + ((m : ℂ) + 1) / 2).re}

private theorem strongChamber_unique (M : Q → ℕ) (f : P → ℂ) (hf : Differentiable ℂ f)
    (hz : ∀ p ∈ strongChamber M, f p = 0) : f = 0 := by
  have hHead (q : Q) (hq : q ∈ chamber r) (z : ℂ) : f (Fin.cons z q) = 0 := by
    let g (w : ℂ) := f (Fin.cons w q)
    have hg : Differentiable ℂ g := hf.comp (differentiable_adjoin q)
    let b : ℝ := max (q 0).re ((m : ℝ) + M q - (((m : ℂ) + 1) / 2).re)
    let w₀ : ℂ := ((b + 1 : ℝ) : ℂ)
    have h₀ : b < w₀.re := by simp [w₀]
    have hEq : g = 0 := by
      refine AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hg.analyticAt w)
        (fun _ _ => analyticAt_const) (z₀ := w₀) ?_
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₀] with w hw
      apply hz
      refine ⟨headTail_chamber q hq w ((le_max_left _ _).trans_lt hw), ?_⟩
      change (m : ℝ) + M (Fin.tail (Fin.cons (α := fun _ : Fin n => ℂ) w q)) ≤ _
      rw [Fin.tail_cons, Fin.cons_zero, Complex.add_re]
      linarith [(le_max_right (q 0).re ((m : ℝ) + M q - (((m : ℂ) + 1) / 2).re)).trans_lt hw]
    exact congrFun hEq z
  let q₀ : Q := fun i => -((i : ℕ) : ℂ)
  have hq₀ : q₀ ∈ chamber r := by
    intro i
    simp only [q₀, Complex.neg_re, Complex.natCast_re, Fin.val_succ, Fin.val_castSucc, Nat.cast_succ,
      Complex.add_re, Complex.one_re]
    linarith
  let p₀ : P := Fin.cons 0 q₀
  have hTail : Continuous (smallerExponents : P → Q) := continuous_pi fun i => continuous_apply i.succ
  have hopen : IsOpen (smallerExponents ⁻¹' chamber r) := isOpen_chamber.preimage hTail
  have hp₀ : p₀ ∈ smallerExponents ⁻¹' chamber r := by
    change Fin.tail (Fin.cons (α := fun _ : Fin n => ℂ) 0 q₀) ∈ chamber r
    rwa [Fin.tail_cons]
  funext p
  let line (z : ℂ) : P := p₀ + z • (p - p₀)
  have hline : Differentiable ℂ line := (differentiable_id.smul_const (p - p₀)).const_add p₀
  have hzero : line 0 = p₀ := by simp [line]
  have hone : line 1 = p := by simp [line, add_comm p₀]
  have hNear : ∀ᶠ z in 𝓝 (0 : ℂ), line z ∈ smallerExponents ⁻¹' chamber r :=
    hline.continuous.continuousAt.preimage_mem_nhds (hzero ▸ hopen.mem_nhds hp₀)
  have hEq : f ∘ line = 0 := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => (hf.comp hline).analyticAt z)
      (fun _ _ => analyticAt_const) (z₀ := (0 : ℂ)) ?_
    filter_upwards [hNear] with z hz
    have he := hHead (smallerExponents (line z)) hz (line z 0)
    change f (Fin.cons (α := fun _ : Fin n => ℂ) (line z 0) (Fin.tail (line z))) = 0 at he
    simpa only [Function.comp_apply, Pi.zero_apply, Fin.cons_self_tail] using he
  simpa only [Function.comp_apply, Pi.zero_apply, hone] using congrFun hEq 1

private theorem fixed_unitary_weight (l : L) (p : P) (k : U) :
    characterWeight (addedCharacter l p) ((m : ℂ) / 2) (determinant (Unitary.toUnits k)) =
      ((determinant (Unitary.toUnits k) : ℂˣ) : ℂ) ^ l 0 := by
  let u : Kc := ⟨Unitary.toUnits k, k.2⟩
  let z := determinant u.val
  have hN : normSqC (z : ℂ) = 1 := normSqC_det_unitary u
  have hs : ‖(z : ℂ)‖ ^ 2 = 1 := by
    change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 at hN
    exact_mod_cast hN
  have hn : ‖(z : ℂ)‖ = 1 := by
    simpa only [Real.sqrt_sq (norm_nonneg (z : ℂ)), Real.sqrt_one] using congrArg Real.sqrt hs
  change ((addedCharacter l p).character z : ℂ) * normSqC (z : ℂ) ^ ((m : ℂ) / 2) = _
  rw [hN, Complex.one_cpow, mul_one, (addedCharacter l p).character_eq, hn]
  simp [z, u, addedCharacter, characterOfParams_weight]

/-- A continued complex Godement integral of a right unitary-finite Schwartz test belongs
to the exact Whittaker model at each irreducible inducing parameter. -/
def ComplexGodementContinuedModelStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P),
    IsIrreducibleGKModule (complexStandardRep n (characterList l p))
      (complexStandardLie n (characterList l p)) →
    ∀ (Φ : 𝓢(Rect, ℂ)),
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : Kc => translateTest k.val Φ)) →
    ∀ W : complexWhittakerModel r (retainedCharacters l p) (-a),
      (fun g => continuedValue ν μ (addedCharacter l p) a (operatorToEntry Φ) W.val g 0) ∈
        complexWhittakerModel (r + 1) (characterList l p) (-a)

set_option maxHeartbeats 1500000 in
theorem complexGodementContinuedModel : ComplexGodementContinuedModelStatement (r := r) := by
  intro ν hν hνr μ a l p hirr Φ hfinite W
  let ω := smallerWeights l
  let q := smallerExponents p
  have hW : W.val ∈ LinearMap.range (continuedJacquet μ a ω q) := by
    rw [← (complexJacquetMultiplicityOne r μ a ω q).2]
    exact W.2
  obtain ⟨w, hw⟩ := hW
  let φ := compactRestriction w.val
  let hφ := compactRestriction_isCompactProfile w.2
  let V := canonicalJacquetFamily μ a ω φ hφ
  let f (u : P) := standardSection (smallerExponents u) φ
  let F (u : P) (g : G) := continuedValue ν μ (characterOfParams (l 0) 0) a (operatorToEntry Φ)
    (V (smallerExponents u)) g (u 0)
  have hv := canonicalJacquetFamily_properties μ a ω φ hφ
  have hF (g : G) : Differentiable ℂ (F · g) :=
    differentiable_generatorValue ν μ a (characterOfParams (l 0) 0) (operatorToEntry Φ) V hv.1 hv.2.1 hv.2.2.1 g
  have hf (u : P) : f u ∈ complexStandardKFinite m (retainedCharacters l u) :=
    standardSection_mem hφ (smallerExponents u)
  choose M₁ hM₁ using fun v : Q => complexJacquetSchwartzEvaluation (r := r) ν l v
  choose M₂ hM₂ using fun v : Q => complexGodementStandardConvergence m (Nat.succ_pos r)
    (characterList ω v) List.length_ofFn
  let M (v : Q) := max (M₁ v) (M₂ v)
  let S := strongChamber M
  let d := addedCharacter l
  have hbound {u : P} (hu : u ∈ S) :
      (m : ℝ) + M (smallerExponents u) ≤ ((d u).exponent + ((m : ℂ) + 1) / 2).re := by
    simpa only [d, addedCharacter, characterOfParams_exponent] using hu.2
  have hconv (u : S) (Ψ : 𝓢(Rect, ℂ)) (g : G) : Integrable (godementSectionIntegrand (d u) Ψ (f u) g) ν := by
    have hc : (M₂ (smallerExponents u) : ℝ) ≤ M (smallerExponents u) := by
      exact_mod_cast (le_max_right (M₁ (smallerExponents u)) (M₂ (smallerExponents u)))
    have hb := (add_le_add (le_refl (m : ℝ)) hc).trans (hbound u.2)
    let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
    let : LocallyCompactSpace H := e.locallyCompactSpace
    let : SecondCountableTopology H := e.secondCountableTopology
    rw [Measure.isMulLeftInvariant_eq_smul ν (complexGeneralLinearHaar m)]
    exact (hM₂ (smallerExponents u) (d u) Ψ (f u) (hf u).1 hb g).smul_measure_nnreal
  let gen (u : S) := godementSection ν (d u) Φ (f u)
  have hgen (u : S) : gen u ∈ Std[l, u.val] := by
    rw [characterList_cons]
    exact schwartzSection_standard ν (d u) _ (f u) (hf u).1 Φ hfinite (hconv u)
  let A := Submodule.span ℂ (range fun u : S => compactRestriction (gen u))
  let : FiniteDimensional ℂ A := finiteDimensional_schwartzSection_profiles ν (fun u : S => d u)
    (fun u : S => f u) (fun k => ((determinant (Unitary.toUnits k) : ℂˣ) : ℂ) ^ l 0)
    (fun u k => fixed_unitary_weight l u k) Φ hfinite hconv
  let ext (u : P) : (U → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := standardSection u
      map_add' x y := (extensionLinear _).map_add x y
      map_smul' c x := (extensionLinear _).map_smul c x }
  have hA : A ≤ (Std[l, (0 : P)]).comap (ext 0) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    exact standardSection_mem (compactRestriction_isCompactProfile (hgen u)) 0
  have hAprofile (v : A) : IsCompactProfile l v.val := by
    have ha : standardSection (0 : P) v.val ∈ Std[l, (0 : P)] := hA v.2
    have h := compactRestriction_isCompactProfile ha
    have hv : compactRestriction (standardSection (0 : P) v.val) = v.val :=
      funext fun k => standardSection_unitary 0 v.val k
    rwa [hv] at h
  let J (u : P) : A →ₗ[ℂ] Std[l, u] := ((ext u).comp A.subtype).codRestrict _
    (fun v => standardSection_mem (hAprofile v) u)
  let T (u : P) : A →ₗ[ℂ] (G → ℂ) := (continuedJacquet μ a l u).comp (J u)
  have hJ (u : P) (v : A) : compactRestriction (J u v).val = v.val :=
    funext fun k => standardSection_unitary u v.val k
  have hT (v : A) (g : G) : Differentiable ℂ (fun u => T u v g) := by
    have he : (fun u => T u v g) = fun u => canonicalJacquetFamily μ a l v.val (hAprofile v) u g := by
      funext u
      change continuedJacquetFamilies μ a l u (J u v) u g = _
      rw [continuedJacquetFamilies_apply]
      exact congrFun (congrFun (ComplexJacquetContinuation.canonicalJacquetFamily_congr μ a l
        (compactRestriction_isCompactProfile (J u v).2) (hAprofile v) (hJ u v)) u) g
    rw [he]
    exact (canonicalJacquetFamily_properties μ a l v.val (hAprofile v)).2.1 g
  have hInj : Function.Injective (T p) := by
    have hB₀ : continuedJacquet μ a l p ≠ 0 := by
      obtain ⟨b, hb⟩ := complexJacquetNonzero (r + 1) μ a l p
      intro h
      exact hb (by rw [h]; rfl)
    apply ((complexJacquetIntertwiner (r + 1) μ a l p).injective_of_irreducible hB₀ hirr).comp
    intro v w he
    apply Subtype.ext
    rw [← hJ p v, ← hJ p w, he]
  have hS (u : P) (hu : u ∈ S) : F u ∈ LinearMap.range (T u) := by
    let u' : S := ⟨u, hu⟩
    let v : A := ⟨compactRestriction (gen u'), Submodule.subset_span ⟨u', rfl⟩⟩
    have he : (J u v).val = gen u' := standardSection_compactRestriction (hgen u')
    have hc : (M₁ (smallerExponents u) : ℝ) ≤ M (smallerExponents u) := by
      exact_mod_cast (le_max_left (M₁ (smallerExponents u)) (M₂ (smallerExponents u)))
    have hb := (add_le_add (le_refl (m : ℝ)) hc).trans hu.2
    let w' : complexStandardKFinite m (retainedCharacters l u) := ⟨f u, hf u⟩
    have hV : continuedJacquet μ a (smallerWeights l) (smallerExponents u) w' = V (smallerExponents u) := by
      change continuedJacquetFamilies μ a ω (smallerExponents u) w' (smallerExponents u) = _
      rw [continuedJacquetFamilies_apply]
      have hprofile : compactRestriction w'.val = φ :=
        funext fun k => standardSection_unitary (smallerExponents u) φ k
      exact congrFun (ComplexJacquetContinuation.canonicalJacquetFamily_congr μ a ω
        (compactRestriction_isCompactProfile w'.2) hφ hprofile) _
    refine ⟨v, ?_⟩
    have hEval := hM₁ (smallerExponents u) u rfl hu.1 hb μ a Φ w' (J u v) he
    change continuedJacquet μ a l u (J u v) = F u
    rw [hEval, hV]
    funext g
    simpa only [F, addedCharacter, characterOfParams_weight, characterOfParams_exponent, zero_add] using
      (continuedValue_eq_shiftedCharacter ν μ (characterOfParams (l 0) 0) a (operatorToEntry Φ)
        (V (smallerExponents u)) g (u 0)).symm
  have h := Langlands.Analysis.mem_range_of_pointwise_analytic_on T F S
    (strongChamber_unique M) hT hF hInj hS
  have hm : F p ∈ complexWhittakerModel (r + 1) (characterList l p) (-a) := by
    rw [(complexJacquetMultiplicityOne (r + 1) μ a l p).2]
    obtain ⟨v, hv⟩ := h
    exact ⟨J p v, hv⟩
  have he : F p = fun g => continuedValue ν μ (addedCharacter l p) a (operatorToEntry Φ) W.val g 0 := by
    funext g
    have hShift := continuedValue_eq_shiftedCharacter ν μ (characterOfParams (l 0) 0) a
      (operatorToEntry Φ) (V q) g (p 0)
    have hV : V q = W.val := hw
    simpa only [F, q, addedCharacter, characterOfParams_exponent, characterOfParams_weight, zero_add, hV]
      using hShift
  rwa [he] at hm

end ComplexGodementContinuedModel
end Langlands.Global.RankinSelbergGlobal
