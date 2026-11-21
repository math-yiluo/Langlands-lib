import Langlands.Global.RankinSelberg.ComplexGodementChamberComparison
import Langlands.Global.RankinSelberg.ComplexGodementKFinite
import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth
import Langlands.Global.RankinSelberg.ComplexGodementUnitaryMajorant

/-! # Joint open-cell comparison for complex Schwartz Godement tests -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator Manifold SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementSchwartzOpenCell

open Langlands.Archimedean (complexStandardModule complexPositionCharacter principalSeries unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Archimedean.ComplexDuality (exists_diagonalUnits_mul_upperUnipotent_mul_unitary)
open ComplexGodementChamberComparison (absoluteCharacter)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant exists_bound_unitaryCompact)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC det_upperUnipotent normSqC_det_unitary)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (isPhasePower)
open Langlands.GeneralLinear (determinant weylLong)
open ArchimedeanLocal (complexNormalizedAbs)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.Shahidi (unipotentProduct unipotentProductMeasure
  continuous_unipotentProduct integrable_unipotentProductMeasure_iff)
open ComplexGodement
open ComplexGodementJacquetComparison (jointKernel openCellIntegral openCellIntegral_godementSection)
open ComplexGodementColumnChange (iteratedKernel)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite unipotentProductMeasure_entryHaar)
open ComplexJacquetChamberConvergence (radialChar sphericalMajorant sphericalMajorant_mem
  sphericalMajorant_ofReal_norm norm_mul_le_sphericalMajorant integrable_openCell_of_borelCovariance)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

private theorem characterWeight_absolute (d : ComplexCharacterData) (s : ℝ) (z : ℂˣ) :
    characterWeight (absoluteCharacter d) (s : ℂ) z = (‖characterWeight d (s : ℂ) z‖ : ℂ) := by
  change (‖(d.character z : ℂ)‖ : ℂ) * (normSqC (z : ℂ)) ^ (s : ℂ) =
    (‖(d.character z : ℂ) * (normSqC (z : ℂ)) ^ (s : ℂ)‖ : ℂ)
  rw [norm_mul, Complex.ofReal_mul, normSqC, ← Complex.ofReal_cpow (sq_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]

private theorem absoluteExponent (ds : List ComplexCharacterData) (i : ℕ) :
    complexPositionExponent (ds.map absoluteCharacter) i = ((complexPositionExponent ds i).re : ℂ) := by
  induction ds generalizing i with
  | nil => simp [complexPositionExponent]
  | cons d ds ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem absolutePosition (ds : List ComplexCharacterData) :
    complexPositionCharacter (ds.map absoluteCharacter) = radialChar (fun i => (complexPositionExponent ds i).re) := by
  funext i z
  induction ds generalizing i with
  | nil => simp [complexPositionCharacter, radialChar, complexPositionExponent]
  | cons d ds ih =>
    cases i with
    | zero =>
      change (‖(d.character z : ℂ)‖ : ℂ) = ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (d.exponent.re : ℂ)
      have h := norm_characterWeight d 0 z
      have h0 : characterWeight d 0 z = (d.character z : ℂ) := by
        change (d.character z : ℂ) * normSqC (z : ℂ) ^ (0 : ℂ) = _
        rw [Complex.cpow_zero, mul_one]
      rw [h0, add_zero] at h
      rw [h, ← Complex.ofReal_cpow (sq_nonneg _)]
      rfl
    | succ i => exact ih i

private theorem mul_eq_ofReal_norm {x y : ℂ} (hx : x = (‖x‖ : ℂ)) (hy : y = (‖y‖ : ℂ)) :
    x * y = (‖x * y‖ : ℂ) := by
  rw [norm_mul, Complex.ofReal_mul, ← hx, ← hy]

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Col" => Fin (r + 1) → ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "w'" => weylLong (r + 1 + 1) ℂ

private theorem det_unipotent {n : ℕ} (u : GeneralLinear.upperUnipotent n ℂ) : determinant u.val = 1 :=
  Units.ext (det_upperUnipotent u)

private theorem integrable_jointKernel_of_majorant
    (ν : Measure G) [SFinite ν] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (he : IsStrictlyDominant (complexPositionExponent (d :: ds)) (r + 1)) (a : ℂˣ)
    (Φ : 𝓢(Rect, ℂ)) (P : 𝓢(Rect, ℂ))
    (hPpos : ∀ X, P X = (‖P X‖ : ℂ)) (hPdom : ∀ X, ‖Φ X‖ ≤ ‖P X‖)
    (hPinv : ∀ (X : Rect) (k : unitaryCompact ℂ (r + 1 + 1)),
      P (mulRightLinearMap (Fin (r + 1)) ℝ k.val.val X) = P X)
    (hconv : ∀ g, Integrable (godementSectionIntegrand (absoluteCharacter d) P
      (sphericalMajorant (r + 1) (fun i => (complexPositionExponent ds i).re)) g) ν)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) (g : G') :
    Integrable (jointKernel d a Φ f g) (((entryHaar μ (r + 1)).prod (rowMeasure μ (r + 1))).prod ν) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  have : SigmaFinite (entryHaar μ (r + 1)) := entryHaar_sigmaFinite μ (r + 1)
  let dn := entryHaar μ (r + 1)
  let dp := dn.prod (rowMeasure μ (r + 1))
  let d₀ := absoluteCharacter d
  let ds₀ := ds.map absoluteCharacter
  let t : ℕ → ℝ := fun i => (complexPositionExponent ds i).re
  let F := sphericalMajorant (r + 1) t
  have hF : F ∈ complexStandardModule (r + 1) ds₀ := by
    change F ∈ principalSeries ℂ (r + 1) (complexPositionCharacter ds₀)
    rw [absolutePosition ds]
    exact (sphericalMajorant_mem (r + 1) t).1
  have hdom : IsStrictlyDominant (complexPositionExponent (d₀ :: ds₀)) (r + 1) := by
    intro i hi
    change (complexPositionExponent ((d :: ds).map absoluteCharacter) (i + 1)).re <
      (complexPositionExponent ((d :: ds).map absoluteCharacter) i).re
    simpa only [absoluteExponent, Complex.ofReal_re] using he i hi
  let b : U × Col → G' := fun p => w' * (unipotentProduct p).val * g
  let K : (U × Col) × G → ℂ := fun p => godementSectionIntegrand d₀ P F (b p.1) p.2
  let S := godementSection ν d₀ P F
  have hSb := godementSection_covariant ν d₀ ds₀ P hF
  let T := sphericalMajorant (r + 1 + 1) (fun i => (complexPositionExponent (d :: ds) i).re)
  have hT : T ∈ complexStandardModule (r + 1 + 1) (d₀ :: ds₀) := by
    change T ∈ principalSeries ℂ (r + 1 + 1) (complexPositionCharacter ((d :: ds).map absoluteCharacter))
    rw [absolutePosition]
    exact (sphericalMajorant_mem _ _).1
  have hSunit (k : unitaryCompact ℂ (r + 1 + 1)) : S k.val = S 1 := by
    have h := godementSection_right_mul ν d₀ P F 1 k.val
    rw [one_mul] at h
    have ht : translateTest k.val (P : Rect → ℂ) = P := funext fun X => hPinv X k
    rw [ht] at h
    have hN : complexNormalizedAbs (determinant k.val : ℂ) = 1 := by
      have hn := normSqC_det_unitary k
      change ((complexNormalizedAbs (determinant k.val : ℂ) : ℝ) : ℂ) = 1 at hn
      exact_mod_cast hn
    let s : ℝ := ((r + 1 : ℕ) : ℝ) / 2
    have hw : characterWeight d₀ (s : ℂ) (determinant k.val) = 1 := by
      rw [characterWeight_absolute, norm_characterWeight, hN, Real.one_rpow, Complex.ofReal_one]
    have hs : (s : ℂ) = (((r + 1 : ℕ) : ℂ) / 2) := by simp [s]
    rw [hs] at hw
    rw [hw, one_mul] at h
    exact h
  have hTunit (k : G') (hk : k ∈ unitaryCompact ℂ (r + 1 + 1)) : T k = 1 := by
    let κ : Matrix.unitaryGroup (Fin (r + 1 + 1)) ℂ := ⟨k.val, hk⟩
    have hκ : Unitary.toUnits κ = k := Units.ext rfl
    rw [← hκ]
    exact Langlands.Archimedean.ComplexPrincipalSeriesExtension.extension_unitary _ _ κ
  have hST : S = fun x => S 1 * T x := by
    funext x
    obtain ⟨z, v, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
    have hs := hSb z v k
    change S (GeneralLinear.Iwasawa.diagonalUnits z * v.val * k) = _ * S k at hs
    rw [hs, hT.2 z v k, hSunit ⟨k, hk⟩, hTunit k hk, mul_one, mul_comm]
  have hS : Continuous S := by
    rw [hST]
    exact continuous_const.mul hT.1.continuous
  have hbig := integrable_openCell_of_borelCovariance μ (isPhasePower (d₀ :: ds₀)) hdom hS hSb g
  have hInner : Integrable (fun p => S (b p)) dp := by
    apply (integrable_unipotentProductMeasure_iff dn (rowMeasure μ (r + 1))
      (fun u => S (w' * u.val * g))).mp
    rwa [unipotentProductMeasure_entryHaar μ (r + 1)]
  let s : ℂ := (((r + 1 : ℕ) : ℂ) / 2)
  let u : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2)
  have hreal : u = ((((r + 1 : ℕ) + 1 : ℝ) / 2 : ℝ) : ℂ) := by simp [u]
  have hweight (h : G) : characterWeight d₀ u (determinant h) =
      (‖characterWeight d u (determinant h)‖ : ℂ) := by
    rw [hreal]
    exact characterWeight_absolute d _ _
  have hKpos (p : (U × Col) × G) : K p = (‖K p‖ : ℂ) := by
    unfold K godementSectionIntegrand
    refine mul_eq_ofReal_norm (mul_eq_ofReal_norm (hPpos _) (sphericalMajorant_ofReal_norm t _)) ?_
    change characterWeight d₀ u (determinant p.2) = (‖characterWeight d₀ u (determinant p.2)‖ : ℂ)
    rw [hweight, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  let A := characterWeight d₀ s (determinant (w' * g))
  have hA : A ≠ 0 := by
    unfold A
    change ((d₀.character (determinant (w' * g)) : ℂ) *
      (normSqC (determinant (w' * g) : ℂ)) ^ s) ≠ 0
    exact mul_ne_zero (d₀.character _).ne_zero (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Langlands.Archimedean.ComplexMaximalParabolicIntegration.normSqC_ne_zero
        (determinant (w' * g)).ne_zero)))
  have hpref (p : U × Col) : characterWeight d₀ s (determinant (b p)) = A := by
    dsimp only [A, b]
    rw [map_mul determinant, map_mul determinant, det_unipotent, mul_one, map_mul determinant]
  have hInnerNorm (p : U × Col) : ‖S (b p)‖ = ‖A‖ * ∫ h, ‖K (p, h)‖ ∂ν := by
    have hfiber : (∫ h, K (p, h) ∂ν) = ((∫ h, ‖K (p, h)‖ ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ fun h => hKpos (p, h))
    change ‖characterWeight d₀ s (determinant (b p)) * (∫ h, K (p, h) ∂ν)‖ = _
    rw [hpref, norm_mul, hfiber, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hb : Continuous b := (continuous_const.mul
    (continuous_subtype_val.comp continuous_unipotentProduct)).mul continuous_const
  have hK : Integrable K (dp.prod ν) := by
    refine (integrable_prod_iff ((continuous_godementSectionIntegrand d₀ P.continuous hF.1.continuous).comp
      ((hb.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact ae_of_all _ fun p => hconv (b p)
    · refine (hInner.norm.const_mul ‖A‖⁻¹).congr (ae_of_all _ fun p => ?_)
      change ‖A‖⁻¹ * ‖S (b p)‖ = ∫ h, ‖K (p, h)‖ ∂ν
      rw [hInnerNorm, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA), one_mul]
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hf.1.continuous
  have hbound (h : G) : ‖f h‖ ≤ C * ‖F h‖ := by
    simpa only [mul_one] using norm_mul_le_sphericalMajorant (isPhasePower ds) hf.2 1
      (fun k hk => by simpa only [mul_one] using hC k hk) h
  have hJoint : Continuous (jointKernel d a Φ f g) := by
    apply ((continuous_godementSectionIntegrand d Φ.continuous hf.1.continuous).comp
      ((hb.comp continuous_fst).prodMk continuous_snd)).mul
    unfold complexWhittakerCharacter
    apply (complexScaledCharacter a).continuous_complex.comp
    exact continuous_finsetSum _ fun i _ => (GeneralLinear.entry i.castSucc i.succ).continuous.comp
      ((continuous_subtype_val.comp continuous_unipotentProduct).comp continuous_fst)
  refine (hK.norm.const_mul C).mono' hJoint.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  unfold jointKernel godementSectionIntegrand complexWhittakerCharacter
  simp only [norm_mul, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex, mul_one]
  calc
    _ ≤ ‖Φ (p.2.val * trailingRows (b p.1).val)‖ * (C * ‖F p.2⁻¹‖) *
        ‖characterWeight d u (determinant p.2)‖ := by
      gcongr
      exact hbound p.2⁻¹
    _ ≤ _ := by
      have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 1 (Subgroup.one_mem _))
      change _ ≤ C * ‖P (p.2.val * trailingRows (b p.1).val) * F p.2⁻¹ *
        characterWeight d₀ u (determinant p.2)‖
      rw [hweight]
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      calc
        _ ≤ ‖P (p.2.val * trailingRows (b p.1).val)‖ * (C * ‖F p.2⁻¹‖) *
            ‖characterWeight d u (determinant p.2)‖ := by
          gcongr
          exact hPdom _
        _ = _ := by ring

variable (r) in
/-- Formula (7.6) for every Schwartz test in a strict chamber with a sufficient
Godement convergence bound on the adjoining exponent. -/
def ComplexGodementSchwartzOpenCellStatement : Prop :=
  ∀ (ν : Measure G) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (ds : List ComplexCharacterData), ds.length = r + 1 →
    ∃ M : ℕ, ∀ (d : ComplexCharacterData),
    IsStrictlyDominant (complexPositionExponent (d :: ds)) (r + 1) →
    ((r + 1 : ℕ) : ℝ) + M ≤ (d.exponent + ((((r + 1 : ℕ) : ℂ) + 1) / 2)).re →
    ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)),
    ∀ f ∈ complexStandardModule (r + 1) ds, ∀ g : G',
      Integrable (jointKernel d a Φ f g)
        (((entryHaar μ (r + 1)).prod (rowMeasure μ (r + 1))).prod ν) ∧
      openCellIntegral a (entryHaar μ (r + 1 + 1)) (godementSection ν d Φ f) g =
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
          characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant g) *
            ∫ h, iteratedKernel (complexScaledCharacter a) μ d (fun X => Φ (X * g.val))
              (openCellIntegral a (entryHaar μ (r + 1)) f) ((((r + 1 : ℕ) : ℂ) + 1) / 2) h ∂ν

set_option maxHeartbeats 700000 in
theorem complexGodementSchwartzOpenCell : ComplexGodementSchwartzOpenCellStatement r := by
  intro ν hν hνr ds hlen
  let eH := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace G := eH.locallyCompactSpace
  let : SecondCountableTopology G := eH.secondCountableTopology
  let ds₀ := ds.map absoluteCharacter
  have hlen₀ : ds₀.length = r + 1 := by simpa only [ds₀, List.length_map] using hlen
  obtain ⟨M, hM⟩ := complexGodementStandardConvergence (r + 1) (Nat.succ_pos r) ds₀ hlen₀
  refine ⟨M, fun d hstrict hd μ a Φ f hf g => ?_⟩
  have : SigmaFinite (entryHaar μ (r + 1)) := entryHaar_sigmaFinite μ (r + 1)
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  obtain ⟨Ψ, hΨ, hΨinv⟩ := complexGodementUnitaryMajorant (r + 1) (r + 1 + 1) Φ
  let P := Ψ.postcompCLM Complex.ofRealCLM
  have hP (X : Rect) : P X = (Ψ X : ℂ) := rfl
  have hPn (X : Rect) : ‖P X‖ = Ψ X := by
    rw [hP, Complex.norm_real, Real.norm_of_nonneg ((norm_nonneg _).trans (hΨ X))]
  have hF : sphericalMajorant (r + 1) (fun i => (complexPositionExponent ds i).re) ∈
      complexStandardModule (r + 1) ds₀ := by
    change _ ∈ principalSeries ℂ (r + 1) (complexPositionCharacter (ds.map absoluteCharacter))
    rw [absolutePosition ds]
    exact (sphericalMajorant_mem _ _).1
  have hd₀ : ((r + 1 : ℕ) : ℝ) + M ≤
      ((absoluteCharacter d).exponent + ((((r + 1 : ℕ) : ℂ) + 1) / 2)).re := by
    simpa only [Complex.add_re, absoluteCharacter, Complex.ofReal_re] using hd
  have hconv (y : G') : Integrable (godementSectionIntegrand (absoluteCharacter d) P
      (sphericalMajorant (r + 1) (fun i => (complexPositionExponent ds i).re)) y) ν := by
    rw [Measure.isMulLeftInvariant_eq_smul ν (complexGeneralLinearHaar (r + 1))]
    exact (hM (absoluteCharacter d) P _ hF hd₀ y).smul_measure_nnreal
  have hint := integrable_jointKernel_of_majorant ν μ d ds hstrict a Φ P
    (fun X => (hP X).trans (congrArg Complex.ofReal (hPn X).symm))
    (fun X => (hΨ X).trans_eq (hPn X).symm)
    (fun X k => congrArg Complex.ofReal (hΨinv X k)) hconv hf g
  refine ⟨hint, ?_⟩
  rw [← unipotentProductMeasure_entryHaar μ (r + 1)]
  exact openCellIntegral_godementSection ν (entryHaar μ (r + 1)) μ d a Φ f g hint

end Langlands.Global.RankinSelbergGlobal.ComplexGodementSchwartzOpenCell
