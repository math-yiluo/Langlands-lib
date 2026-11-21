import Langlands.Global.RankinSelberg.ComplexLocalMatchedMatrixExpansion
import Langlands.Global.RankinSelberg.ComplexLocalEqualShiftedProducts
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerDual

/-! # Entire products for a unitary-finite square test in the equal-rank unfolding -/

noncomputable section

open Filter MeasureTheory
open Langlands.Archimedean Langlands.Archimedean.ComplexDuality
open Langlands.GeneralLinear Langlands.Automorphic Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n
local notation "ι" => inverseTranspose n ℂ
local notation "μK" => unitaryHaar n

/-- The reflection multiplier of the two unscaled unfolded double integrals. -/
def equalDoublePhase (d : ComplexCharacterData) (ds es : List ComplexCharacterData) : ℂ :=
  complexCentralSign ds ^ ds.length *
    ((complexCentralSign es ^ ds.length * complexCentralSign ds ^ es.length) *
      (complexPairStandardEpsilon es ds : ℂ)) * (complexPairStandardEpsilon [d] es : ℂ)

theorem equalDoublePhase_ne_zero (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    equalDoublePhase d ds es ≠ 0 := by
  have hsign (xs : List ComplexCharacterData) : complexCentralSign xs ≠ 0 := by
    intro h
    have hs := complexCentralSign_sq xs
    rw [h] at hs
    norm_num at hs
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hsign ds))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hsign es)) (pow_ne_zero _ (hsign ds)))
      (complexPairStandardEpsilon es ds).ne_zero)) (complexPairStandardEpsilon [d] es).ne_zero

/-- The two Gamma denominator products in the equal-rank unfolded integral. -/
def equalDoubleDenominator (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (z s : ℂ) : ℂ :=
  (complexPairLFactor es ds).denominator s * (complexPairLFactor [d] es).denominator (s + z)

/-- The two Gamma denominator products for the inverse adjoining character. -/
def equalDoubleDualDenominator (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (z s : ℂ) : ℂ :=
  equalDoubleDenominator d.inv (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv) (-z) s

private theorem stripGrowth_add {f g : ℂ → ℂ}
    (hf : HasStripExponentialGrowth f) (hg : HasStripExponentialGrowth g) :
    HasStripExponentialGrowth (fun s => f s + g s) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hf⟩ := hf a b
  obtain ⟨D, L, U, hD, _, hg⟩ := hg a b
  refine ⟨C + D, max K L, max T U, add_nonneg hC hD, hK.trans (le_max_left _ _), ?_⟩
  intro s ha hb hs
  rw [add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hf s ha hb ((le_max_left _ _).trans hs)).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hg s ha hb ((le_max_right _ _).trans hs)).trans ?_
    gcongr
    exact le_max_right _ _

private theorem stripGrowth_sum {k : ℕ} (F : Fin k → ℂ → ℂ)
    (hF : ∀ j, HasStripExponentialGrowth (F j)) :
    HasStripExponentialGrowth (fun s => ∑ j, F j s) := by
  suffices ∀ S : Finset (Fin k), HasStripExponentialGrowth (fun s => ∑ j ∈ S, F j s) from
    this Finset.univ
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    exact fun a b => ⟨0, 0, 0, le_rfl, le_rfl, fun s _ _ _ => by simp⟩
  | insert j S hj ih =>
    simpa only [Finset.sum_insert hj] using stripGrowth_add (hF j) ih

private theorem stripGrowth_shift {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (z : ℂ) :
    HasStripExponentialGrowth (fun s => f (s + z)) := by
  simpa only [Complex.ofReal_one, div_one] using hf.div_add z (c := 1) one_pos

private theorem stripGrowth_tilt {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (v : ℂ) :
    HasStripExponentialGrowth (fun s => f (s + (v + s))) := by
  convert hf.div_add (v / 2) (c := 1 / 2) (by norm_num) using 1
  funext s
  congr 1
  push_cast
  ring

/-- The finite compact products give a single entire function whose two chamber
traces are the normalized unfolded integral and its reflected Fourier partner. -/
def ComplexLocalEqualFiniteSquareNormalizedStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData), ds.length = m →
  ∀ (e : Fin n → ComplexCharacterData) (U : complexWhittakerModel r ds 1)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-1) B →
  ∀ (f : complexStandardKFinite n (List.ofFn e)) (Ψ Ψd : 𝓢(Mat, ℂ)),
    (Ψd : Mat → ℂ) = complexMatrixFourier 1 Ψ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc => fun X => Ψ ((k.val⁻¹).val * X))) →
    (∀ V : complexWhittakerModel (r + 1) (List.ofFn e) (-1),
      HasComplexPairNormalizedGrowth (List.ofFn e) ds (-1) (complexCentralSign ds ^ m)
        (complexUnequalIntegral gap D₁ V.val U.val)
        (complexUnequalDualIntegral gap (-1) D₁ V.val U.val)) →
    ∃ F : ℂ × ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, HasStripExponentialGrowth (fun s => F (z, s))) ∧
      (∀ v : ℂ, HasStripExponentialGrowth (fun s => F (v + s, s))) ∧
      (∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
        F (z, s) = equalDoubleDenominator d ds (List.ofFn e) z s *
          complexEqualUnfoldedIntegral D.groupHaar D₁
            (shiftedCharacter d z).character.toMonoidHom Ψ U.val (B f) s) ∧
      (∃ τ σ : ℝ, ∀ z s : ℂ, τ < (-z).re → σ < s.re →
        F (z, 1 - s) = (equalDoublePhase d ds (List.ofFn e))⁻¹ *
          (equalDoubleDualDenominator d ds (List.ofFn e) z s *
            complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d.inv (-z)).character.toMonoidHom
              Ψd (ud U.val) (wd (B f)) s))

set_option maxHeartbeats 1800000 in
theorem complexLocalEqualFiniteSquareNormalized :
    ComplexLocalEqualFiniteSquareNormalizedStatement (r := r) := by
  intro D D₁ d ds hds e U B hB f Ψ Ψd hΨd hfin hAdj
  let es := List.ofFn e
  have hes : es.length = n := List.length_ofFn
  let V : complexWhittakerModel (r + 1) es (-1) :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let Ud : complexWhittakerModel r (dualData ds) (-1) := ⟨ud U.val, dualFunction_mem hds U.2⟩
  let Vd : complexWhittakerModel (r + 1) (dualData es) (-(-1 : ℂˣ)) :=
    ⟨wd V.val, dualFunction_mem hes V.2⟩
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  obtain ⟨κ, k, Vj, bj, Z, Zd, hκ, hP, hPd, hJ, hj, β, hβ⟩ :=
    complexLocalMatchedMatrixGrowth (r := r + 1) D.groupHaar d e (-1) B hB f Ψ hfin
  let i := complexUnitaryInverseTranspose n
  have hi : Continuous i := continuous_complexUnitaryInverseTranspose
  have hjd (j : Fin k) : wd (Vj j) ∈ complexWhittakerModel (r + 1) (dualData es) (-(-1 : ℂˣ)) :=
    dualFunction_mem hes (hj j).1
  have hη : (d.inv.character : ℂˣ →* ℂˣ).comp invMonoidHom = d.character.toMonoidHom := by
    rw [inverseCharacter_hom]
    ext z
    simp
  have hPd' (X : Mat) : (∫ k, κ k * complexCompactMatrixTranslate
      (d.inv.character.toMonoidHom.comp invMonoidHom) Ψd (i k) X ∂μK) = Ψd X := by
    change (∫ k, κ k * complexCompactMatrixTranslate
      ((d.inv.character : ℂˣ →* ℂˣ).comp invMonoidHom) Ψd (i k) X ∂μK) = Ψd X
    rw [hη, hΨd]
    exact hPd X
  obtain ⟨τ, σ, hProd⟩ := complexLocalEqualShiftedProducts D D₁ μK (MonoidHom.id Kc)
    continuous_id κ hκ 1 d ds es U V (complexMatrixEntryToOperator Ψ) hP k Vj bj Z
    (fun j => (hj j).1) (fun x g => (hJ x g).1)
    ⟨β, fun s hs j => ⟨(hβ s hs j).1, (hβ s hs j).2.2.1⟩⟩
  obtain ⟨τd, σd, hProdd⟩ := complexLocalEqualShiftedProducts D D₁ μK i hi κ hκ
    (-1) d.inv (dualData ds) (dualData es) Ud Vd (complexMatrixEntryToOperator Ψd) hPd' k
    (fun j => wd (Vj j)) (fun j => bj j ∘ ι) Zd hjd (fun x g => (hJ x g).2)
    ⟨β, fun s hs j => by
      change Integrable (complexJacquetMatrixIntegrand d.inv (bj j ∘ ι) Ψd s) D.groupHaar ∧
        Zd j s = ∫ g, complexJacquetMatrixIntegrand d.inv (bj j ∘ ι) Ψd s g ∂D.groupHaar
      rw [hΨd]
      exact ⟨(hβ s hs j).2.1, (hβ s hs j).2.2.2⟩⟩
  have hANorm (j : Fin k) :=
    hAdj ⟨Vj j, (hj j).1⟩
  have hZNorm (j : Fin k) := (hj j).2.2.2.2
  choose A Ad hA hAd hAg hAdg hAR hAE using hANorm
  choose M Md hM hMd hMg hMdg hMR hME using hZNorm
  choose ρ hρ using hAR
  choose ρm hρm using hMR
  obtain ⟨u, hu⟩ := (Set.finite_range ρ).bddAbove
  obtain ⟨v, hv⟩ := (Set.finite_range ρm).bddAbove
  let F (p : ℂ × ℂ) := ∑ j, A j p.2 * M j (p.2 + p.1)
  let Fd (p : ℂ × ℂ) := ∑ j, Ad j p.2 * Md j (p.2 - p.1)
  have hF : Differentiable ℂ F := Differentiable.fun_sum fun j _ =>
    ((hA j).comp differentiable_snd).mul
      ((hM j).comp (differentiable_snd.add differentiable_fst))
  have hRef (z s : ℂ) : Fd (z, 1 - s) = equalDoublePhase d ds es * F (z, s) := by
    dsimp only [F, Fd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (1 - s) - z = 1 - (s + z) by ring, hAE j s, hME j (s + z),
      complexPairEpsilon_neg_one, complexPairEpsilon_one, one_mul, equalDoublePhase, hds]
    ring
  refine ⟨F, hF, fun z => stripGrowth_sum _ (fun j => (hAg j).mul (stripGrowth_shift (hMg j) z)),
    fun v => stripGrowth_sum _ (fun j => (hAg j).mul (stripGrowth_tilt (hMg j) v)), ?_, ?_⟩
  · refine ⟨max τ 0, max σ (max u v), fun z s hz hs => ?_⟩
    have hRaw := hProd z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)
    rw [coe_complexMatrixEntryToOperator] at hRaw
    change complexEqualUnfoldedIntegral D.groupHaar D₁
      (shiftedCharacter d z).character.toMonoidHom Ψ U.val V.val s = _ at hRaw
    have hsj (j : Fin k) : ρ j < s.re :=
      (hu (Set.mem_range_self j)).trans_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
    have hmk (j : Fin k) : ρm j < (s + z).re := by
      rw [Complex.add_re]
      linarith [hv (Set.mem_range_self j),
        (le_max_right u v).trans_lt ((le_max_right σ _).trans_lt hs), (le_max_right τ 0).trans_lt hz]
    change F (z, s) = _ * complexEqualUnfoldedIntegral D.groupHaar D₁
      (shiftedCharacter d z).character.toMonoidHom Ψ U.val V.val s
    rw [hRaw, Finset.mul_sum]
    dsimp only [F]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hρ j s (hsj j)).1, (hρm j (s + z) (hmk j)).1]
    unfold equalDoubleDenominator
    ring
  · refine ⟨max τd 0, max σd (max u v), fun z s hz hs => ?_⟩
    have hRaw := hProdd (-z) s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)
    rw [coe_complexMatrixEntryToOperator] at hRaw
    change complexEqualUnfoldedIntegral D.groupHaar D₁
      (shiftedCharacter d.inv (-z)).character.toMonoidHom Ψd Ud.val Vd.val s = _ at hRaw
    have hsj (j : Fin k) : ρ j < s.re :=
      (hu (Set.mem_range_self j)).trans_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
    have hmk (j : Fin k) : ρm j < (s - z).re := by
      rw [sub_eq_add_neg, Complex.add_re]
      linarith [hv (Set.mem_range_self j),
        (le_max_right u v).trans_lt ((le_max_right σd _).trans_lt hs), (le_max_right τd 0).trans_lt hz]
    have hN :
        Fd (z, s) = equalDoubleDualDenominator d ds es z s *
          complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d.inv (-z)).character.toMonoidHom
            Ψd Ud.val Vd.val s := by
      rw [hRaw, Finset.mul_sum]
      dsimp only [Fd, Ud, Vd]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hρ j s (hsj j)).2, (hρm j (s - z) (hmk j)).2,
        complexUnequalDualIntegral_adjacent]
      unfold equalDoubleDualDenominator equalDoubleDenominator
      simp only [List.map_cons, List.map_nil, sub_eq_add_neg]
      ring
    have he := hRef z (1 - s)
    rw [sub_sub_cancel, hN] at he
    rw [he, ← mul_assoc, inv_mul_cancel₀ (equalDoublePhase_ne_zero d ds es), one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
