import Langlands.Global.RankinSelberg.RealPrincipalSeriesFactors
import Langlands.Global.RankinSelberg.RealUniformLocalTheoryReduction

/-! # The real-place functional equation from the principal-series equations -/

noncomputable section

universe u
open MeasureTheory
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean Langlands.Weil.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace RealPrincipalSeries

private theorem clear_primal_denominator {d : ℂ} (hd : d ≠ 0) (e dd sign m md : ℂ) :
    d⁻¹ * md = sign * e * dd⁻¹ * m ↔ md = sign * (e * d / dd) * m := by
  rw [inv_mul_eq_iff_eq_mul₀ hd, div_eq_mul_inv]
  have h : d * (sign * e * dd⁻¹ * m) = sign * (e * d * dd⁻¹) * m := by ac_rfl
  rw [h]

/-- The expanded factors in an equation package can be replaced by the original factors.
The measures, integral kernels, integral functions and scalar sign are fixed. -/
theorem equationPackage_of_expand {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ} {Kd : ℂ → Y → ℂ}
    {Z Zd : ℂ → ℂ} {sign : ℂ}
    (ds es : List RealBlock) (b : ℝˣ) (c : NNReal) (hc : 0 < c)
    (hEq : RealJacquet.EquationPackage μ ν K Kd Z Zd
      (fun s => ((realPairLFactor (expand ds) (expand es)).denominator s)⁻¹)
      (fun s => ((realPairLFactor ((expand ds).map RealLocalJacquet.dualBlock)
        ((expand es).map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon (expand ds) (expand es) b c hc s : ℂ)) sign) :
    RealJacquet.EquationPackage μ ν K Kd Z Zd
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign := by
  obtain ⟨σ, M, Md, hK, hKd, hZ, hZd, hM, hMd, hZM, hZdMd, hFE⟩ := hEq
  refine ⟨σ, M, Md, hK, hKd, hZ, hZd, hM, hMd, hZM, hZdMd, ?_⟩
  have hNonzero (F : ReciprocalEntire) : ∀ᶠ s in Filter.codiscrete ℂ, F.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr F.denominator_eventually_ne_zero
  filter_upwards [hFE, pairMultiplier_expand ds es b c hc,
    hNonzero (realPairLFactor (expand ds) (expand es)), hNonzero (realPairLFactor ds es)] with
    s hs hGamma hExpanded hOriginal
  have hCleared : Md (1 - s) = sign * pairMultiplier (expand ds) (expand es) b c hc s * M s :=
    (clear_primal_denominator hExpanded _ _ _ _ _).mp hs
  rw [hGamma] at hCleared
  exact (clear_primal_denominator hOriginal _ _ _ _ _).mpr hCleared

private theorem expand_eq_map_character (ds : List RealBlock) :
    ∃ cs : List RealCharacterData, expand ds = cs.map RealBlock.character := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons d ds ih =>
    obtain ⟨cs, hcs⟩ := ih
    cases d with
    | character d =>
      exact ⟨d :: cs, congrArg (RealBlock.character d :: ·) hcs⟩
    | induced d =>
      let k := d.weight.natAbs
      let c₁ := Archimedean.RealJacquetFrobenius.charData (RealGammaReflection.positionParity k)
        (d.exponent + (k : ℂ) / 2)
      let c₂ := Archimedean.RealJacquetFrobenius.charData 0 (d.exponent - (k : ℂ) / 2)
      exact ⟨c₁ :: c₂ :: cs, congrArg (RealBlock.character c₁ :: RealBlock.character c₂ :: ·) hcs⟩

end RealPrincipalSeries

open RealPrincipalSeries ArchimedeanLocal

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := borel _
local instance (r : ℕ) : BorelSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

namespace RealJacquet

theorem UnequalEquation.of_expand {r t : ℕ} {h : t < r} {a b : ℝˣ}
    {D : RealQuotientMeasureData t} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ} {ds es : List RealBlock} {sign : ℂ}
    (hEq : UnequalEquation h a D W W' (expand ds) (expand es)
      ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock)
      b sign) :
    UnequalEquation h a D W W' ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) b sign :=
  equationPackage_of_expand ds es b _ _ hEq

theorem EqualEquation.of_expand {r : ℕ} {a b : ℝˣ} {D : RealQuotientMeasureData r}
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ} {ds es : List RealBlock} {sign : ℂ}
    (hEq : EqualEquation a b D W W' Φ (expand ds) (expand es)
      ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock)
      sign) :
    EqualEquation a b D W W' Φ ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) sign :=
  equationPackage_of_expand ds es b _ _ hEq

end RealJacquet

/-- The uniform coefficient space of a block presentation embeds in the uniform coefficient
space of the corresponding principal series, as submodules of the same function space. -/
def RealUniformPrincipalSeriesInclusionStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ (a : ℝˣ),
    realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r (expand ds) a

/-- The uniform unequal-rank equation specialized to two real character lists. -/
def RealLocalPrincipalUnequalJacquetStatement : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (h : t < r) (cs bs : List RealCharacterData),
    let ds := cs.map RealBlock.character
    let es := bs.map RealBlock.character
    realRank ds = r + 1 → realRank es = t + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData t)
      (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
      W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel t es (-a) →
      RealJacquet.UnequalEquation h a D W W' ds es
        (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (-a)
        ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) *
          (RealJacquet.determinant es (-1) : ℂ))

/-- The uniform positive equal-rank equation specialized to two real character lists. -/
def RealLocalPrincipalPositiveEqualJacquetStatement : Prop := by
  classical
  exact
  ∀ (r : ℕ), 0 < r → ∀ (cs bs : List RealCharacterData),
    let ds := cs.map RealBlock.character
    let es := bs.map RealBlock.character
    realRank ds = r + 1 → realRank es = r + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r)
      (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel r es (-a) →
      RealJacquet.EqualEquation a (-a) D W W' Φ ds es
        (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock)
        ((RealJacquet.determinant ds (-1) : ℂ) ^ r)

theorem realLocalUniformUnequalJacquet_of_principal
    (hI : RealUniformPrincipalSeriesInclusionStatement)
    (hU : RealLocalPrincipalUnequalJacquetStatement) : RealLocalUniformUnequalJacquetStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  obtain ⟨cs, hcs⟩ := expand_eq_map_character ds
  obtain ⟨bs, hbs⟩ := expand_eq_map_character es
  have hEq := hU r t h cs bs
    (by simpa only [← hcs, realRank_expand] using hds)
    (by simpa only [← hbs, realRank_expand] using hes) a D W W'
    (by simpa only [← hcs] using hI r ds hds a hW)
    (by simpa only [← hbs] using hI t es hes (-a) hW')
  rw [← hcs, ← hbs] at hEq
  apply RealJacquet.UnequalEquation.of_expand
  simpa only [determinant_expand] using hEq

theorem realLocalUniformPositiveEqualJacquet_of_principal
    (hI : RealUniformPrincipalSeriesInclusionStatement)
    (hE : RealLocalPrincipalPositiveEqualJacquetStatement) :
    RealLocalUniformPositiveEqualJacquetStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  obtain ⟨cs, hcs⟩ := expand_eq_map_character ds
  obtain ⟨bs, hbs⟩ := expand_eq_map_character es
  have hEq := hE r hr cs bs
    (by simpa only [← hcs, realRank_expand] using hds)
    (by simpa only [← hbs, realRank_expand] using hes) a D W W' Φ
    (by simpa only [← hcs] using hI r ds hds a hW)
    (by simpa only [← hbs] using hI r es hes (-a) hW')
  rw [← hcs, ← hbs] at hEq
  apply RealJacquet.EqualEquation.of_expand
  simpa only [determinant_expand] using hEq

/-- The principal-series equations, uniform coefficient inclusion, and actual dual
denominator comparison imply the exact real-place functional equation. -/
def RealPlacePrincipalSeriesReductionStatement : Prop :=
  RealUniformPrincipalSeriesInclusionStatement →
  RealLocalPrincipalUnequalJacquetStatement →
  RealLocalPrincipalPositiveEqualJacquetStatement →
  RealPlaceContragredientPairLStatement.{u} →
  RealPlaceFunctionalEquationStatement.{u}

theorem realPlacePrincipalSeriesReduction : RealPlacePrincipalSeriesReductionStatement.{u} := by
  intro hI hU hE hD
  exact realPlaceUniformLocalTheoryReduction (realLocalUniformUnequalJacquet_of_principal hI hU)
    (realLocalUniformPositiveEqualJacquet_of_principal hI hE) hD

end Langlands.Global.RankinSelbergGlobal
