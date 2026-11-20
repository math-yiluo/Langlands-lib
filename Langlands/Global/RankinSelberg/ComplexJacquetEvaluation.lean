import Langlands.Global.RankinSelberg.ComplexJacquetUniformContinuation

/-! # Linear evaluation of the entire complex Jacquet family -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (complexPositionCharacter unitaryCompact
  rightTranslation_mem_kFiniteFunctions_principalSeries)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (eq_of_eqOn_unitary extensionLinear)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.Whittaker (rightTranslation)
open ComplexCompactProfileFamily (characterList IsCompactProfile standardSection standardSection_mem
  standardSection_unitary compactRestriction compactRestriction_isCompactProfile standardSection_compactRestriction)
open ComplexGodementGeneratorFamily (eq_of_differentiable_eqOn_chamber isStrictlyDominant_characterList)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetChamberIntertwiner (chamberIntertwiner openCellIntegral_left_mul)
open ComplexJacquetUnipotentMeasure (entryHaar)

attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "P" => Fin (r + 1) → ℂ
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "L" => Fin (r + 1) → ℤ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite (r + 1) (characterList l p)

/-- The entire continuation determined by a fixed compact profile and the chosen entry Haar. -/
def canonicalJacquetFamily (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (φ : U → ℂ)
    (hφ : IsCompactProfile l φ) : P → G → ℂ :=
  Classical.choose (complexJacquetUniformContinuation r μ a l φ hφ)

theorem canonicalJacquetFamily_properties (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (φ : U → ℂ)
    (hφ : IsCompactProfile l φ) :
    let J := canonicalJacquetFamily μ a l φ hφ
    (∀ p, Continuous (J p)) ∧ (∀ g, Differentiable ℂ (fun p => J p g)) ∧
    (∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) J) ∧
    ∀ p ∈ chamber r, ∀ g, J p g = openCellIntegral a (entryHaar μ (r + 1)) (standardSection p φ) g :=
  Classical.choose_spec (complexJacquetUniformContinuation r μ a l φ hφ)

theorem canonicalJacquetFamily_unique (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (φ : U → ℂ)
    (hφ : IsCompactProfile l φ) (F : P → G → ℂ) (hF : ∀ g, Differentiable ℂ (fun p => F p g))
    (hch : ∀ p ∈ chamber r, ∀ g, F p g = openCellIntegral a (entryHaar μ (r + 1)) (standardSection p φ) g) :
    F = canonicalJacquetFamily μ a l φ hφ := by
  have hJ := canonicalJacquetFamily_properties μ a l φ hφ
  funext p g
  have h := eq_of_differentiable_eqOn_chamber (hF g) (hJ.2.1 g) (by
    intro q hq
    exact (hch q hq g).trans (hJ.2.2.2 q hq g).symm)
  exact congrFun h p

theorem canonicalJacquetFamily_left_mul (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (φ : U → ℂ)
    (hφ : IsCompactProfile l φ) (p : P) (u : N) (g : G) :
    canonicalJacquetFamily μ a l φ hφ p (u.val * g) =
      complexWhittakerCharacter (-a) u.val * canonicalJacquetFamily μ a l φ hφ p g := by
  have hJ := canonicalJacquetFamily_properties μ a l φ hφ
  have h := eq_of_differentiable_eqOn_chamber (hJ.2.1 (u.val * g))
    ((hJ.2.1 g).const_mul (complexWhittakerCharacter (-a) u.val)) (by
      intro q hq
      change canonicalJacquetFamily μ a l φ hφ q (u.val * g) =
        complexWhittakerCharacter (-a) u.val * canonicalJacquetFamily μ a l φ hφ q g
      rw [hJ.2.2.2 q hq (u.val * g), hJ.2.2.2 q hq g]
      exact openCellIntegral_left_mul μ a (standardSection q φ) u g)
  exact congrFun h p

private def standardSectionLinear (p : P) : (U → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := standardSection p
  map_add' f g := (extensionLinear _).map_add f g
  map_smul' c f := (extensionLinear _).map_smul c f

/-- Transfer an exact compact-finite section to new exponents by retaining its compact profile. -/
def transferProfile (l : L) (p q : P) : Std[l, p] →ₗ[ℂ] Std[l, q] :=
  ((standardSectionLinear q).comp (compactRestriction.comp (Std[l, p]).subtype)).codRestrict (Std[l, q])
    (fun f => standardSection_mem (compactRestriction_isCompactProfile f.2) q)

@[simp]
theorem transferProfile_val (l : L) (p q : P) (f : Std[l, p]) :
    (transferProfile l p q f).val = standardSection q (compactRestriction f.val) := rfl

theorem transferProfile_self (l : L) (p : P) (f : Std[l, p]) : transferProfile l p p f = f :=
  Subtype.ext (standardSection_compactRestriction f.2)

theorem transferProfile_apply_unitary (l : L) (p q : P) (f : Std[l, p]) (k : K) :
    (transferProfile l p q f).val k.val = f.val k.val := by
  let x : U := ⟨k.val.val, k.2⟩
  have hx : Unitary.toUnits x = k.val := Units.ext rfl
  rw [← hx, transferProfile_val, standardSection_unitary]
  rfl

theorem transferProfile_rightTranslation (l : L) (p q : P) (k : K) (f f' : Std[l, p])
    (h : f'.val = rightTranslation ℂ G k.val f.val) :
    (transferProfile l p q f').val = rightTranslation ℂ G k.val (transferProfile l p q f).val := by
  have hmem := rightTranslation_mem_kFiniteFunctions_principalSeries (complexPositionCharacter (characterList l q))
    (unitaryCompact ℂ (r + 1)) (transferProfile l p q f).2 k.2
  refine eq_of_eqOn_unitary (transferProfile l p q f').2.1 hmem.1 fun g hg => ?_
  let u : K := ⟨g, hg⟩
  change (transferProfile l p q f').val u.val = (transferProfile l p q f).val (u * k).val
  rw [transferProfile_apply_unitary, transferProfile_apply_unitary, h]
  rfl

private def chamberEvaluationAt (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L)
    (p q : P) (hq : q ∈ chamber r) : Std[l, p] →ₗ[ℂ] (G → ℂ) :=
  (chamberIntertwiner μ (characterList l q) a (isStrictlyDominant_characterList l hq)).comp (transferProfile l p q)

private def sectionJacquetFamily (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P) (f : Std[l, p]) : P → G → ℂ :=
  canonicalJacquetFamily μ a l (compactRestriction f.val) (compactRestriction_isCompactProfile f.2)

private theorem sectionJacquet_holomorphic (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P)
    (f : Std[l, p]) (g : G) : Differentiable ℂ (fun q => sectionJacquetFamily μ a l p f q g) :=
  (canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile f.2)).2.1 g

private theorem sectionJacquet_chamber (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P)
    (f : Std[l, p]) (q : P) (hq : q ∈ chamber r) (g : G) :
    sectionJacquetFamily μ a l p f q g = chamberEvaluationAt μ a l p q hq f g :=
  (canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile f.2)).2.2.2 q hq g

/-- The linear Jacquet family attached to an exact compact-finite standard module at any
reference parameter. Values at other parameters use the same compact profile. -/
def continuedJacquetFamilies (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P) :
    Std[l, p] →ₗ[ℂ] (P → G → ℂ) where
  toFun := sectionJacquetFamily μ a l p
  map_add' f h := by
    funext q g
    have he := eq_of_differentiable_eqOn_chamber (sectionJacquet_holomorphic μ a l p (f + h) g)
      ((sectionJacquet_holomorphic μ a l p f g).add (sectionJacquet_holomorphic μ a l p h g)) (by
        intro z hz
        change sectionJacquetFamily μ a l p (f + h) z g =
          sectionJacquetFamily μ a l p f z g + sectionJacquetFamily μ a l p h z g
        rw [sectionJacquet_chamber μ a l p (f + h) z hz g, sectionJacquet_chamber μ a l p f z hz g,
          sectionJacquet_chamber μ a l p h z hz g, map_add]
        rfl)
    exact congrFun he q
  map_smul' c f := by
    funext q g
    have he := eq_of_differentiable_eqOn_chamber (sectionJacquet_holomorphic μ a l p (c • f) g)
      ((sectionJacquet_holomorphic μ a l p f g).const_mul c) (by
        intro z hz
        change sectionJacquetFamily μ a l p (c • f) z g = c * sectionJacquetFamily μ a l p f z g
        rw [sectionJacquet_chamber μ a l p (c • f) z hz g, sectionJacquet_chamber μ a l p f z hz g,
          map_smul]
        rfl)
    exact congrFun he q

@[simp]
theorem continuedJacquetFamilies_apply (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P) (f : Std[l, p]) :
    continuedJacquetFamilies μ a l p f =
      canonicalJacquetFamily μ a l (compactRestriction f.val) (compactRestriction_isCompactProfile f.2) := rfl

/-- The evaluation of the linear Jacquet family at the inducing parameter of the input vector. -/
def continuedJacquet (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P) : Std[l, p] →ₗ[ℂ] (G → ℂ) :=
  (LinearMap.proj (R := ℂ) p).comp (continuedJacquetFamilies μ a l p)

theorem continuedJacquet_chamber (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P)
    (hp : p ∈ chamber r) (f : Std[l, p]) :
    continuedJacquet μ a l p f = openCellIntegral a (entryHaar μ (r + 1)) f.val := by
  funext g
  have h := sectionJacquet_chamber μ a l p f p hp g
  change continuedJacquet μ a l p f g = openCellIntegral a (entryHaar μ (r + 1)) (transferProfile l p p f).val g at h
  rwa [transferProfile_self] at h

theorem continuedJacquetFamilies_rightTranslation (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p q : P)
    (k : K) (f f' : Std[l, p]) (h : f'.val = rightTranslation ℂ G k.val f.val) :
    continuedJacquetFamilies μ a l p f' q = rightTranslation ℂ G k.val (continuedJacquetFamilies μ a l p f q) := by
  funext g
  have he := eq_of_differentiable_eqOn_chamber (sectionJacquet_holomorphic μ a l p f' g)
    (sectionJacquet_holomorphic μ a l p f (g * k.val)) (by
      intro z hz
      change sectionJacquetFamily μ a l p f' z g = sectionJacquetFamily μ a l p f z (g * k.val)
      rw [sectionJacquet_chamber μ a l p f' z hz g, sectionJacquet_chamber μ a l p f z hz (g * k.val)]
      change openCellIntegral a (entryHaar μ (r + 1)) (transferProfile l p z f').val g =
        openCellIntegral a (entryHaar μ (r + 1)) (transferProfile l p z f).val (g * k.val)
      rw [transferProfile_rightTranslation l p z k f f' h]
      unfold openCellIntegral
      apply integral_congr_ae (ae_of_all _ fun u => ?_)
      change (transferProfile l p z f).val ((Langlands.GeneralLinear.weylLong (r + 1) ℂ * u.val * g) * k.val) * _ = _
      rw [mul_assoc])
  exact congrFun he q

variable (r) in
/-- The continued Jacquet values of exact compact-finite standard vectors are linear, have
left Whittaker and right unitary equivariance, and match the exact chamber values. -/
def ComplexJacquetEvaluationStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P),
    (∀ (f : Std[l, p]) (u : N) (g : G),
      continuedJacquet μ a l p f (u.val * g) = complexWhittakerCharacter (-a) u.val * continuedJacquet μ a l p f g) ∧
    (∀ (k : K) (f f' : Std[l, p]), f'.val = rightTranslation ℂ G k.val f.val →
      continuedJacquet μ a l p f' = rightTranslation ℂ G k.val (continuedJacquet μ a l p f)) ∧
    (p ∈ chamber r → ∀ f : Std[l, p], continuedJacquet μ a l p f = openCellIntegral a (entryHaar μ (r + 1)) f.val)

theorem complexJacquetEvaluation : ComplexJacquetEvaluationStatement r := by
  intro μ a l p
  exact ⟨fun f u g => canonicalJacquetFamily_left_mul μ a l _ (compactRestriction_isCompactProfile f.2) p u g,
    fun k f f' h => continuedJacquetFamilies_rightTranslation μ a l p p k f f' h,
    fun hp f => continuedJacquet_chamber μ a l p hp f⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
