import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient

/-! # The real-place equations from ascending character quotients -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

universe u

open RealPrincipalSeries ArchimedeanLocal

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := borel _
local instance (r : ℕ) : BorelSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

namespace RealPrincipalSeries

/-- The determinant sign agrees with the original inducing presentation. -/
theorem determinant_ascendingExpand (ds : List RealBlock) (a : ℝˣ) :
    RealJacquet.determinant (ascendingExpand ds) a = RealJacquet.determinant ds a := by
  rw [← determinant_expand ds a]
  exact ((ascendingExpand_perm ds).map (fun d : RealBlock => d.determinant a)).prod_eq

/-- A position permutation leaves the equation package unchanged, including
the factors of the termwise dual presentation. -/
theorem equationPackage_of_presentation_perm {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ} {Kd : ℂ → Y → ℂ}
    {Z Zd : ℂ → ℂ} {sign : ℂ}
    {ds ds' es es' : List RealBlock} (hd : ds.Perm ds') (he : es.Perm es')
    (b : ℝˣ) (c : NNReal) (hc : 0 < c)
    (hEq : RealJacquet.EquationPackage μ ν K Kd Z Zd
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign) :
    RealJacquet.EquationPackage μ ν K Kd Z Zd
      (fun s => ((realPairLFactor ds' es').denominator s)⁻¹)
      (fun s => ((realPairLFactor (ds'.map RealLocalJacquet.dualBlock)
        (es'.map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds' es' b c hc s : ℂ)) sign := by
  simpa only [realPairLFactor_perm hd he,
    realPairLFactor_perm (hd.map RealLocalJacquet.dualBlock) (he.map RealLocalJacquet.dualBlock),
    realPairEpsilon_perm hd he b c hc] using hEq

end RealPrincipalSeries

/-- The character principal-series unequal-rank equation suffices for all real blocks. -/
theorem realLocalUniformUnequalJacquet_of_ascending
    (hU : RealLocalPrincipalUnequalJacquetStatement) :
    RealLocalUniformUnequalJacquetStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  have hEq := hU r t h (ascendingCharacters ds) (ascendingCharacters es)
    ((realRank_ascendingExpand ds).trans hds) ((realRank_ascendingExpand es).trans hes)
    a D W W' (uniformModel_le_ascendingExpand r ds hds a hW)
      (uniformModel_le_ascendingExpand t es hes (-a) hW')
  have he : RealJacquet.UnequalEquation h a D W W' (expand ds) (expand es)
      ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock) (-a)
      ((RealJacquet.determinant (ascendingExpand ds) (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant (ascendingExpand es) (-1) : ℂ)) :=
    equationPackage_of_presentation_perm (ascendingExpand_perm ds) (ascendingExpand_perm es) _ _ _ hEq
  apply RealJacquet.UnequalEquation.of_expand
  simpa only [determinant_ascendingExpand] using he

/-- The character principal-series positive equal-rank equation suffices for all real blocks. -/
theorem realLocalUniformPositiveEqualJacquet_of_ascending
    (hE : RealLocalPrincipalPositiveEqualJacquetStatement) :
    RealLocalUniformPositiveEqualJacquetStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  have hEq := hE r hr (ascendingCharacters ds) (ascendingCharacters es)
    ((realRank_ascendingExpand ds).trans hds) ((realRank_ascendingExpand es).trans hes)
    a D W W' Φ (uniformModel_le_ascendingExpand r ds hds a hW)
      (uniformModel_le_ascendingExpand r es hes (-a) hW')
  have he : RealJacquet.EqualEquation a (-a) D W W' Φ (expand ds) (expand es)
      ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock)
      ((RealJacquet.determinant (ascendingExpand ds) (-1) : ℂ) ^ r) :=
    equationPackage_of_presentation_perm (ascendingExpand_perm ds) (ascendingExpand_perm es) _ _ _ hEq
  apply RealJacquet.EqualEquation.of_expand
  simpa only [determinant_ascendingExpand] using he

/-- Both character principal-series equations and the actual dual factor
comparison imply the exact real-place proposition. -/
def RealPlaceAscendingPrincipalSeriesReductionStatement : Prop :=
  RealLocalPrincipalUnequalJacquetStatement →
    RealLocalPrincipalPositiveEqualJacquetStatement →
    RealPlaceContragredientPairLStatement.{u} →
    RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceAscendingPrincipalSeriesReduction :
    RealPlaceAscendingPrincipalSeriesReductionStatement.{u} :=
  fun hU hE hD => realPlaceUniformLocalTheoryReduction
    (realLocalUniformUnequalJacquet_of_ascending hU)
    (realLocalUniformPositiveEqualJacquet_of_ascending hE) hD

end Langlands.Global.RankinSelbergGlobal
