import Langlands.Global.RankinSelberg.ComplexJacquetEvaluation

/-! # Exact canonical Jacquet evaluation of compact Godement generators -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (characterOfParams unitaryCompact)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extensionLinear)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.GeneralLinear (determinant)
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open ComplexCompactProfileFamily (characterList IsCompactProfile compactRestriction
  compactRestriction_isCompactProfile standardSection standardSection_mem
  standardSection_unitary standardSection_compactRestriction)
open ComplexGodement (HasFullRowRank godementSection godementTests
  translateTest godementSection_right_mul godementSectionLinear complexGodementKFinite
  addedCharacter retainedCharacters smallerSection smallerWeights smallerExponents SmallerProfile
  characterList_cons characterWeight complexGodementCompactHolomorphic)
open ComplexGodementGeneratorFamily (generatorFamily complexGodementGeneratorFamily
  eq_of_differentiable_eqOn_chamber)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetUnipotentMeasure (entryHaar)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "P" => Fin (r + 1) → ℂ
local notation "P'" => Fin (r + 1 + 1) → ℂ
local notation "L" => Fin (r + 1 + 1) → ℤ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1 + 1)) ℂ
local notation "K" => unitaryCompact ℂ (r + 1 + 1)
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Test" => OperatorSchwartz (r + 1) (r + 1 + 1)
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p)

private def translatedTestHomeomorph (k : G') : Rect ≃ₜ Rect where
  toFun X := X * k.val
  invFun X := X * k⁻¹.val
  left_inv X := by
    change (X * k.val) * k⁻¹.val = X
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    change (X * k⁻¹.val) * k.val = X
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

private theorem translateTest_mem (k : G') {Φ : Rect → ℂ}
    (hΦ : Φ ∈ godementTests (r + 1)) : translateTest k Φ ∈ godementTests (r + 1) := by
  let e := translatedTestHomeomorph k
  have hsub : tsupport (translateTest k Φ) ⊆ e ⁻¹' tsupport Φ :=
    closure_minimal (fun X hX => subset_tsupport Φ hX) ((isClosed_tsupport Φ).preimage e.continuous)
  refine ⟨hΦ.1.comp e.continuous,
    HasCompactSupport.of_support_subset_isCompact (e.isCompact_preimage.mpr hΦ.2.1)
      ((subset_tsupport _).trans hsub), fun X hX => ?_⟩
  obtain ⟨Y, hY⟩ := hΦ.2.2 (e X) (hsub hX)
  exact ⟨k.val * Y, by rw [← Matrix.mul_assoc]; exact hY⟩

private theorem weight_at_unitary (l : L) (p q : P') (k : K) :
    characterWeight (addedCharacter l p) (((r + 1 : ℕ) : ℂ) / 2) (determinant k.val) =
      ((addedCharacter l q).character (determinant k.val) : ℂ) := by
  let z := determinant k.val
  have hN : normSqC (z : ℂ) = 1 := normSqC_det_unitary k
  have hs : ‖(z : ℂ)‖ ^ 2 = 1 := by
    change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 at hN
    exact_mod_cast hN
  have hn : ‖(z : ℂ)‖ = 1 := by
    simpa only [Real.sqrt_sq (norm_nonneg (z : ℂ)), Real.sqrt_one] using congrArg Real.sqrt hs
  change ((addedCharacter l p).character z : ℂ) * normSqC (z : ℂ) ^ (((r + 1 : ℕ) : ℂ) / 2) =
    ((addedCharacter l q).character z : ℂ)
  rw [hN, Complex.one_cpow, mul_one, (addedCharacter l p).character_eq, (addedCharacter l q).character_eq, hn]
  simp [addedCharacter]

/-- The compact generator belongs to the exact standard module at every radial parameter. -/
theorem godementSection_mem_standardKFinite (ν : Measure G) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] (l : L) (Φ : Test) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    (hfinite : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => translateTest k.val Φ)))
    (f : SmallerProfile l) (p : P') :
    godementSection ν (addedCharacter l p) Φ (smallerSection p f) ∈ Std[l, p] := by
  rw [characterList_cons]
  exact complexGodementKFinite (r + 1) ν (addedCharacter l p) (retainedCharacters l p)
    Φ (Φ.smooth ⊤) hΦ hfull hfinite (smallerSection p f) (standardSection_mem f.2 (smallerExponents p)).1

private def profileExtensionLinear (p : P') : (U → ℂ) →ₗ[ℂ] (G' → ℂ) where
  toFun := standardSection p
  map_add' f h := (extensionLinear _).map_add f h
  map_smul' c f := (extensionLinear _).map_smul c f

set_option maxHeartbeats 800000 in
private theorem exists_finite_span_generatorProfiles (ν : Measure G) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] (l : L) (Φ : Test) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    (hfinite : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => translateTest k.val Φ)))
    (f : SmallerProfile l) :
    ∃ A : Submodule ℂ (U → ℂ), FiniteDimensional ℂ A ∧ (∀ v : A, IsCompactProfile l v.val) ∧
      ∀ p : P', compactRestriction (godementSection ν (addedCharacter l p) Φ (smallerSection p f)) ∈ A := by
  let orbit (k : U) := translateTest (Unitary.toUnits k) Φ
  let V := Submodule.span ℂ (range orbit)
  let gen (p : P') := godementSection ν (addedCharacter l p) Φ (smallerSection p f)
  let A := Submodule.span ℂ (range fun p => compactRestriction (gen p))
  have hV : V ≤ (Submodule.span ℂ (range fun k : K => translateTest k.val Φ)) := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩
  let : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hV
  have hTests : V ≤ godementTests (r + 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact translateTest_mem (Unitary.toUnits k) ⟨Φ.continuous, hΦ, hfull⟩
  let v (k : U) : V := ⟨orbit k, Submodule.subset_span ⟨k, rfl⟩⟩
  let T (p : P') : V →ₗ[ℂ] (G' → ℂ) :=
    (godementSectionLinear ν (addedCharacter l p) (standardSection_mem f.2 (smallerExponents p)).1.1.continuous).comp
      (Submodule.inclusion hTests)
  let b := Module.finBasis ℂ V
  let θ (k : U) : ℂ := ((addedCharacter l (0 : P')).character (determinant (Unitary.toUnits k)) : ℂ)
  let coeff (i : Fin (Module.finrank ℂ V)) (k : U) := θ k * b.repr (v k) i
  let A₀ := Submodule.span ℂ (range coeff)
  let : FiniteDimensional ℂ A₀ := FiniteDimensional.span_of_finite _ (finite_range coeff)
  have hA₀ : A ≤ A₀ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    have he : compactRestriction (gen p) = ∑ i, T p (b i) 1 • coeff i := by
      funext k
      let eval := (LinearMap.proj (R := ℂ) (1 : G')).comp (T p)
      have hb := congrArg eval (b.sum_repr (v k))
      simp only [map_sum, map_smul] at hb
      have hKg : compactRestriction (gen p) k = θ k * eval (v k) := by
        have hw := weight_at_unitary l p 0 (⟨Unitary.toUnits k, k.2⟩ : K)
        have hg := godementSection_right_mul ν (addedCharacter l p) Φ (smallerSection p f)
          (1 : G') (Unitary.toUnits k)
        rw [one_mul, hw] at hg
        exact hg
      rw [hKg, ← hb, Finset.mul_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      change θ k * (b.repr (v k) i * T p (b i) 1) = T p (b i) 1 * (θ k * b.repr (v k) i)
      ring
    change compactRestriction (gen p) ∈ A₀
    rw [he]
    exact Submodule.sum_mem A₀ fun i _ => Submodule.smul_mem A₀ _ (Submodule.subset_span ⟨i, rfl⟩)
  let T₀ := profileExtensionLinear (0 : P')
  have hA : A ≤ (Std[l, (0 : P')]).comap T₀ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact standardSection_mem (compactRestriction_isCompactProfile
      (godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite f p)) 0
  refine ⟨A, Submodule.finiteDimensional_of_le hA₀, ?_, fun p => Submodule.subset_span ⟨p, rfl⟩⟩
  intro v
  have hT : standardSection (0 : P') v.val ∈ Std[l, (0 : P')] := hA v.2
  have hc : compactRestriction (standardSection (0 : P') v.val) = v.val :=
    funext fun k => standardSection_unitary 0 v.val k
  have h := compactRestriction_isCompactProfile hT
  rwa [hc] at h

/-- Changing the compact profile by an equality preserves the canonical evaluation. -/
theorem canonicalJacquetFamily_congr {m : ℕ} (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : Fin (m + 1) → ℤ) {φ ψ : Matrix.unitaryGroup (Fin (m + 1)) ℂ → ℂ}
    (hφ : IsCompactProfile l φ) (hψ : IsCompactProfile l ψ) (h : φ = ψ) :
    canonicalJacquetFamily μ a l φ hφ = canonicalJacquetFamily μ a l ψ hψ := by
  subst ψ
  rfl

variable (r) in
/-- For a compact full-row-rank finite test the canonical evaluation of its Godement section
coincides with the continued partial Fourier integral at all inducing parameters. -/
def ComplexJacquetGeneratorEvaluationStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (Φ : Test) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    (hfinite : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => translateTest k.val Φ)))
    (f : SmallerProfile l) (p : P'),
    continuedJacquet μ a l p ⟨godementSection ν (addedCharacter l p) Φ (smallerSection p f),
      godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite f p⟩ =
      generatorFamily ν μ a l Φ (canonicalJacquetFamily μ a (smallerWeights l) f.val f.2) p

set_option maxHeartbeats 1200000 in
theorem complexJacquetGeneratorEvaluation : ComplexJacquetGeneratorEvaluationStatement r := by
  intro ν hνf hν hνr μ a l Φ hΦ hfull hfinite f p
  obtain ⟨A, hAfin, hA, hgen⟩ := exists_finite_span_generatorProfiles ν l Φ hΦ hfull hfinite f
  let gen (q : P') := godementSection ν (addedCharacter l q) Φ (smallerSection q f)
  let v (q : P') : A := ⟨compactRestriction (gen q), hgen q⟩
  let T₀ : A →ₗ[ℂ] Std[l, (0 : P')] := ((profileExtensionLinear 0).comp A.subtype).codRestrict _
    (fun u => standardSection_mem (hA u) 0)
  let J := (continuedJacquetFamilies μ a l 0).comp T₀
  let b := Module.finBasis ℂ A
  have hT (v : A) : compactRestriction (T₀ v).val = v.val :=
    funext fun k => standardSection_unitary 0 v.val k
  have hJdiff (v : A) (g : G') : Differentiable ℂ (fun q => J v q g) :=
    (canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile (T₀ v).2)).2.1 g
  have hJch (v : A) (q : P') (hq : q ∈ chamber (r + 1)) (g : G') :
      J v q g = openCellIntegral a (entryHaar μ (r + 1 + 1)) (standardSection q v.val) g := by
    have h := (canonicalJacquetFamily_properties μ a l _
      (compactRestriction_isCompactProfile (T₀ v).2)).2.2.2 q hq g
    change J v q g = _ at h
    rwa [hT v] at h
  let smaller : P' →ₗ[ℂ] P := {
    toFun := smallerExponents
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let smallerCLM : P' →L[ℂ] P := smaller.toContinuousLinearMap
  have hgenDiff (g : G') : Differentiable ℂ (fun q => gen q g) := by
    have hfc := (ComplexCompactProfileFamily.continuous_standardSection_family f.2.1).comp
      ((smallerCLM.continuous.comp continuous_fst).prodMk continuous_snd)
    have hfd (h : G) := (ComplexCompactProfileFamily.differentiable_standardSection f.val h).comp
      smallerCLM.differentiable
    exact complexGodementCompactHolomorphic ν (l 0) _
      (ContinuousLinearMap.proj 0 : P' →L[ℂ] ℂ).differentiable Φ Φ.continuous hΦ hfull
      (fun q => smallerSection q f) hfc hfd g
  have hcoord (i : Fin (Module.finrank ℂ A)) : Differentiable ℂ (fun q => b.coord i (v q)) := by
    obtain ⟨k, x, c, hx⟩ := Langlands.Archimedean.InductionStages.exists_eval_sum A (b.coord i)
    have he : (fun q => b.coord i (v q)) = fun q => ∑ j : Fin k, c j * gen q (Unitary.toUnits (x j)) :=
      funext fun q => hx (v q)
    rw [he]
    exact Differentiable.fun_sum fun j _ => (hgenDiff (Unitary.toUnits (x j))).const_mul _
  have hDiff (g : G') : Differentiable ℂ (fun q => J (v q) q g) := by
    have he : (fun q => J (v q) q g) = fun q => ∑ i, b.coord i (v q) * J (b i) q g := by
      funext q
      have he := congrArg J (b.sum_repr (v q))
      simp only [map_sum, map_smul] at he
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply] using
        (congrFun (congrFun he q) g).symm
    rw [he]
    exact Differentiable.fun_sum fun i _ => (hcoord i).mul (hJdiff (b i) g)
  let W := canonicalJacquetFamily μ a (smallerWeights l) f.val f.2
  have hw := canonicalJacquetFamily_properties μ a (smallerWeights l) f.val f.2
  have hF := complexGodementGeneratorFamily (r := r) ν μ a l Φ hΦ hfull f W
    hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
  have hcompare (g : G') : J (v p) p g = generatorFamily ν μ a l Φ W p g := by
    apply congrFun (eq_of_differentiable_eqOn_chamber (hDiff g) (hF.1 g) ?_) p
    intro q hq
    change J (v q) q g = generatorFamily ν μ a l Φ W q g
    rw [hJch (v q) q hq g]
    change openCellIntegral a (entryHaar μ (r + 1 + 1))
      (standardSection q (compactRestriction (gen q))) g = _
    rw [standardSection_compactRestriction (godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite f q)]
    exact (hF.2.2.2.2 q hq g).symm
  let fp : Std[l, p] := ⟨gen p, godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite f p⟩
  have heq := canonicalJacquetFamily_congr μ a l
    (compactRestriction_isCompactProfile fp.2)
    (compactRestriction_isCompactProfile (T₀ (v p)).2) (hT (v p)).symm
  funext g
  exact (congrFun (congrFun heq p) g).trans (hcompare g)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
