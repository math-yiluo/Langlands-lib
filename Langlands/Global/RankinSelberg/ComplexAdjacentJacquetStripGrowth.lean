import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Global.RankinSelberg.ComplexAdjacentCompactAverage
import Langlands.Global.RankinSelberg.ComplexAdjacentCompactWeight
import Langlands.Global.RankinSelberg.ComplexAdjacentProductExpansion
import Langlands.Global.RankinSelberg.ComplexAdjacentSplitIntegrals
import Langlands.Global.RankinSelberg.ComplexLocalCompactMatchedProjection
import Langlands.Global.RankinSelberg.ComplexLocalJacquetEndpointConvergence
import Langlands.Global.RankinSelberg.ComplexSquareZetaCoefficientAverage
import Langlands.Global.RankinSelberg.ComplexSquareZetaPolynomialAverage
import Langlands.Global.RankinSelberg.ComplexSquareZetaStripGrowth
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist

/-! # Complex adjacent-rank strip growth for split tests -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic
open Langlands.GeneralLinear Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ComplexDeterminantTwist (detCharacter detCharacter_mul detCharacter_inv_mul
  detCharacter_mul_mem_principalSeries complexPositionCharacter_map_mul)
open ComplexGodement (characterWeight normPower exists_height_bound_standard)
open ComplexGodementAddedCharacter (continuedValue)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexSquareZeta (compactCoefficient leftAverageInv zetaKernel squarePolynomialGaussian
  leftAverageInv_squarePolynomialGaussian finiteDimensional_leftSquarePolynomialGaussian)
open ComplexGodementGaussianPolynomial (Coordinates)
open ComplexJacquet (complexAdjacentCompactWeight complexLocalCompactMatchedProjection
  complexLocalCompactProjectionReduction complexCompactMatrixTranslate
  complexLocalEqualEndpointConvergence)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 2) ℂ
local notation "Kc" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "columnProd" => ComplexGodementColumnProduct.columnProduct

private abbrev inducedUnitaryMeasurableSpace (r : ℕ) :
    MeasurableSpace (unitaryCompact ℂ (r + 1)) := inferInstance

private theorem inducedUnitaryMeasurableSpace_eq (r : ℕ) :
    inducedUnitaryMeasurableSpace r = ComplexDuality.unitaryMeasurableSpace (r + 1) :=
  (borel_comap (f := (Subtype.val :
    unitaryCompact ℂ (r + 1) → Langlands.GeneralLinear (r + 1) ℂ))).symm

private def integralWith {α : Type*} (m : MeasurableSpace α) (μ : @Measure α m) (f : α → ℂ) :
    ℂ :=
  letI := m
  ∫ x, f x ∂μ

private theorem exists_transportedHaar {α : Type*} [Group α] [TopologicalSpace α]
    {m m' : MeasurableSpace α} (h : m = m') (μ : @Measure α m)
    (hf : letI := m; IsFiniteMeasure μ) (hh : letI := m; μ.IsHaarMeasure) :
    ∃ μ' : @Measure α m', (letI := m'; IsFiniteMeasure μ') ∧
      (letI := m'; μ'.IsHaarMeasure) ∧ ∀ f, integralWith m μ f = integralWith m' μ' f := by
  subst m'
  exact ⟨μ, hf, hh, fun _ => rfl⟩

private theorem twistedCoefficient_eq (κ : Measure Kc) (d : ComplexCharacterData)
    (w : Kc → ℂ) (f : G → ℂ) (g : G) :
    compactCoefficient κ id (fun k => detCharacter d.character⁻¹ k.val * w k)
      (fun x => detCharacter d.character x * f x) g =
        detCharacter d.character g * compactCoefficient κ id w f g := by
  unfold compactCoefficient
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only [id_eq, detCharacter_mul]
  calc
    _ = (detCharacter d.character⁻¹ k.val * detCharacter d.character k.val) *
        (detCharacter d.character g * (w k * f (k.val * g))) := by ring
    _ = _ := by rw [detCharacter_inv_mul, one_mul]

private theorem singleton_pairFactor (d : ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData) :
    complexLFactor (List.ofFn fun j => (es j).mul d) = complexPairLFactor [d] (List.ofFn es) := by
  apply ReciprocalEntire.ext
  funext s
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_ofFn, denominator_complexLFactor, List.prod_ofFn, Function.comp_apply,
    ComplexCharacterData.lFactor, ComplexCharacterData.mul, add_comm d.weight, add_comm d.exponent]

private def SquareTraceProperty (R : (ℂ → ℂ) → Prop) (μ : Measure G) (κ : Measure Kc)
    [IsFiniteMeasure κ] (d : ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData)
    (Φ : 𝓢(Mat, ℂ)) : Prop :=
  let ds := fun i => (es i).mul d
  ∀ (w : Kc → ℂ) (hw : Continuous w) (f : G → ℂ), f ∈ complexStandardModule (r + 1) (List.ofFn ds) →
    ∃ (τ : ℝ) (Z : ℂ → ℂ), Differentiable ℂ Z ∧ R Z ∧
      ∀ s : ℂ, τ < s.re → Z s = (complexLFactor (List.ofFn ds)).denominator s *
        ∫ g, zetaKernel (leftAverageInv κ id continuous_id w hw Φ) f s g ∂μ

private theorem twistedCoefficientNormalization (R : (ℂ → ℂ) → Prop)
    (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (d : ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData)
    (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ) (w : Kc → ℂ)
    (hf : f ∈ complexStandardModule (r + 1) (List.ofFn es)) (hw : Continuous w)
    (hSquare : SquareTraceProperty R μ κ d es Φ) :
    let J (s : ℂ) (g : G) := Φ g.val * characterWeight d ((r : ℂ) / 2 + s) (determinant g) *
      compactCoefficient κ id w f g
    ∃ (σ : ℝ) (Z : ℂ → ℂ), Differentiable ℂ Z ∧ R Z ∧
      ∀ s : ℂ, σ < s.re → Integrable (J s) μ ∧
        Z s = (complexPairLFactor [d] (List.ofFn es)).denominator s * ∫ g, J s g ∂μ := by
  intro J
  let ds := fun i => (es i).mul d
  let f' (g : G) := detCharacter d.character g * f g
  let w' (k : Kc) := detCharacter d.character⁻¹ k.val * w k
  have hf' : f' ∈ complexStandardModule (r + 1) (List.ofFn ds) := by
    change f' ∈ complexStandardModule (r + 1)
      (List.ofFn ((fun x : ComplexCharacterData => x.mul d) ∘ es))
    rw [← List.map_ofFn]
    exact detCharacter_mul_mem_principalSeries d.character
      (fun i z => complexPositionCharacter_map_mul d (List.ofFn es) i
        (by simpa only [List.length_ofFn] using i.isLt) z) hf
  have hw' : Continuous w' :=
    ((Units.continuous_val.comp (d.character⁻¹.continuous.comp
      determinantContinuous.continuous)).comp continuous_subtype_val).mul hw
  obtain ⟨τ, Z, hZd, hZg, hZ⟩ := hSquare w' hw' f' hf'
  obtain ⟨M, hM⟩ := exists_height_bound_standard (Nat.succ_pos r) (List.ofFn ds) List.length_ofFn
  obtain ⟨C, hC, hbound⟩ := hM f' hf'
  have hJ (s : ℂ) : J s = zetaKernel Φ (compactCoefficient κ id w' f') s := by
    funext g
    change Φ g.val * characterWeight d ((r : ℂ) / 2 + s) (determinant g) *
      compactCoefficient κ id w f g = _
    rw [zetaKernel, show compactCoefficient κ id w' f' g =
      detCharacter d.character g * compactCoefficient κ id w f g from twistedCoefficient_eq κ d w f g]
    rw [show (((r + 1 : ℕ) : ℂ) - 1) / 2 = (r : ℂ) / 2 by simp, add_comm s]
    change Φ g.val * ((d.character (determinant g) : ℂ) *
      normPower ((r : ℂ) / 2 + s) (determinant g)) * compactCoefficient κ id w f g = _
    simp only [detCharacter]
    ring
  let q := ((((r + 1 : ℕ) : ℂ) - 1) / 2).re
  refine ⟨max τ ((r + 1 : ℝ) + M + |q|), Z, hZd, hZg, fun s hs => ?_⟩
  have hsM : (r + 1 : ℝ) + M ≤ (s + (((r + 1 : ℕ) : ℂ) - 1) / 2).re := by
    rw [Complex.add_re]
    change (r + 1 : ℝ) + M ≤ s.re + q
    have ht := (le_max_right τ ((r + 1 : ℝ) + M + |q|)).trans_lt hs
    linarith [neg_abs_le q]
  have hAvg := ComplexSquareZeta.complexSquareZetaCoefficientAverage
    μ κ id continuous_id w' hw' Φ f' hf'.1.continuous M C hC hbound s (by simpa using hsM)
  rw [hJ s]
  refine ⟨hAvg.1, ?_⟩
  rw [hAvg.2, ← singleton_pairFactor d es]
  exact hZ s ((le_max_left _ _).trans_lt hs)

private theorem finiteSumStripGrowth {l : ℕ} {f : Fin l → ℂ → ℂ}
    (hf : ∀ i, HasStripExponentialGrowth (f i)) :
    HasStripExponentialGrowth (fun s => ∑ i, f i s) := by
  intro a b
  choose C K T hC hK hB using fun i => hf i a b
  refine ⟨∑ i, C i, ∑ i, K i, ∑ i, |T i|, Finset.sum_nonneg (fun i _ => hC i),
    Finset.sum_nonneg (fun i _ => hK i), fun s ha hb hs => (norm_sum_le _ _).trans ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hTi : T i ≤ ∑ j, |T j| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (T j)) hi)
  have hKi : K i ≤ ∑ j, K j := Finset.single_le_sum (fun j _ => hK j) hi
  exact (hB i s ha hb (hTi.trans hs)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKi (abs_nonneg _))) (hC i))

private theorem cons_pairFactor (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es = (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    complexLFactor_append]

open scoped Langlands.Archimedean.ComplexDuality

private def AdjacentJacquetNormalization (R : (ℂ → ℂ) → Prop) : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData),
    ds.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a))
    (B : complexStandardKFinite (r + 1) (List.ofFn es) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner r (List.ofFn es) a B →
  ∀ (f : complexStandardKFinite (r + 1) (List.ofFn es))
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ (k.val⁻¹.val * X))) →
    (∀ V : complexWhittakerModel r (List.ofFn es) a,
      ∃ A : OrdinaryIntegralNormalization (complexEqualIntegral D U V (splitRowTransform a φ))
        (fun s => ((complexPairLFactor ds (List.ofFn es)).denominator s)⁻¹),
        R A.value) →
    (letI : MeasurableSpace Kc := inducedUnitaryMeasurableSpace r
     ∀ (κ₀ : Measure Kc) [IsFiniteMeasure κ₀] [κ₀.IsHaarMeasure],
       SquareTraceProperty R D.groupHaar κ₀ d es Φ) →
    let W (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g 0
    ∃ N : OrdinaryIntegralNormalization (complexUnequalIntegral gap D W (B f))
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹),
      R N.value

private theorem adjacentJacquetNormalization (R : (ℂ → ℂ) → Prop)
    (hR : ∀ (l : ℕ) (c : ℂ) (A Z : Fin l → ℂ → ℂ),
      (∀ j, R (A j)) → (∀ j, R (Z j)) → R (fun s => c * ∑ j, A j s * Z j s)) :
    AdjacentJacquetNormalization (r := r) R := by
  intro D _ κ _ _ a d ds es hds U B hB f Φ φ hΦ hA hSquare W
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace G := e.locallyCompactSpace
  let : SecondCountableTopology G := e.secondCountableTopology
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : SFinite μ := inferInstance
  let V : complexWhittakerModel r (List.ofFn es) a :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let V₀ : complexWhittakerModel r (List.ofFn es) (-(-a)) := ⟨V, by simpa only [neg_neg] using V.2⟩
  let ψ := splitRowTransform a φ
  obtain ⟨σ, hσ⟩ := complexAdjacentSplitIntegrals D a d 0 Φ φ ds (List.ofFn es) hds List.length_ofFn U V
  obtain ⟨w, hw, hwfin, hRec, _⟩ :=
    complexAdjacentCompactWeight (r := r) κ d.character.toMonoidHom d.character.continuous a Φ hΦ
  have hRec' (X : Mat) :
      (∫ k, w k * (d.character ((determinant (id k).val)⁻¹) : ℂ) *
        Φ ((id k).val⁻¹.val * X) ∂κ) = Φ X := by
    calc
      _ = ∫ k, w k * complexCompactMatrixTranslate (d.character.toMonoidHom.comp invMonoidHom) Φ k X ∂κ := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        change w k * (d.character ((determinant k.val)⁻¹) : ℂ) * Φ (k.val⁻¹.val * X) =
          w k * ((d.character ((determinant k.val)⁻¹) : ℂ) * Φ (k.val⁻¹.val * X))
        exact mul_assoc _ _ _
      _ = Φ X := hRec X
  obtain ⟨τ, hτ⟩ := complexAdjacentCompactAverage D μ κ id continuous_id w hw d ((r : ℂ) / 2)
    Φ ψ hΦ hRec' (-a) ds (List.ofFn es) U V₀
  obtain ⟨p, hp, hp'⟩ :=
    complexLocalCompactMatchedProjection (r := r) (List.ofFn es) a κ inferInstance w hw hwfin B hB f
  obtain ⟨l, V', w', hw', hExpansion⟩ :=
    complexLocalCompactProjectionReduction (r := r) (List.ofFn es) a κ inferInstance w hw hwfin f B hB p hp hp'
  obtain ⟨κ₀, hκ₀f, hκ₀h, hκ₀⟩ := exists_transportedHaar
    (inducedUnitaryMeasurableSpace_eq r).symm κ inferInstance inferInstance
  have hCoeff (w₀ : Kc → ℂ) (g : G) :
      compactCoefficient κ₀ id w₀ f.val g = ∫ k, w₀ k * f.val (k.val * g) ∂κ :=
    (hκ₀ (fun k => w₀ k * f.val (k.val * g))).symm
  let V₁ (j : Fin l) : complexWhittakerModel r (List.ofFn es) a := ⟨V' j, (hw' j).1⟩
  choose A hAg using fun j => hA (V₁ j)
  choose τA hτA using fun j => (A j).eq_on_right
  choose τE hτE using fun j => complexLocalEqualEndpointConvergence hds List.length_ofFn (-a)
    D U.val (V' j) ψ U.2 (by simpa only [neg_neg] using (hw' j).1)
  choose τZ Z hZd hZg hτZ using fun j =>
    @twistedCoefficientNormalization r R μ inferInstance κ₀ hκ₀f hκ₀h
      d es Φ f.val (w' j) f.2.1 (hw' j).2 (@hSquare κ₀ hκ₀f hκ₀h)
  obtain ⟨tZ, htZ⟩ := complexPairLFactor_denominator_ne_zero [d] (List.ofFn es)
  obtain ⟨β, hβ⟩ := (Set.finite_range fun j => max (τA j) (max (τE j) (τZ j))).bddAbove
  let c : ℂ := (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ)
  let N (s : ℂ) := c * ∑ j, (A j).value s * Z j s
  have hAd (j : Fin l) : Differentiable ℂ (A j).value :=
    fun s => ((A j).analytic s (mem_univ _)).differentiableAt
  have hNd : Differentiable ℂ N :=
    (Differentiable.fun_sum fun j _ => (hAd j).mul (hZd j)).const_mul c
  have hNg : R N := hR l c (fun j => (A j).value) Z hAg hZg
  refine ⟨⟨N, fun s _ => hNd.analyticAt s, ⟨max (max σ τ) (max β tZ), fun s hs => ?_⟩⟩, hNg⟩
  have hs' := (le_max_left (max σ τ) (max β tZ)).trans_lt hs
  have hs'' := (le_max_right (max σ τ) (max β tZ)).trans_lt hs
  have hAll (j : Fin l) : max (τA j) (max (τE j) (τZ j)) < s.re :=
    (hβ (Set.mem_range_self j)).trans_lt ((le_max_left β tZ).trans_lt hs'')
  have hE (j : Fin l) := (hτE j s ((le_max_left (τE j) (τZ j)).trans_lt
    ((le_max_right (τA j) _).trans_lt (hAll j)))).1
  have hZ (j : Fin l) := hτZ j s ((le_max_right (τE j) (τZ j)).trans_lt
    ((le_max_right (τA j) _).trans_lt (hAll j)))
  have hZne := htZ s ((le_max_right β tZ).trans_lt hs'')
  have heq := (hσ s ((le_max_left σ τ).trans_lt hs')).2.2.1
  have havg := (hτ s ((le_max_right σ τ).trans_lt hs')).2
  let C (j : Fin l) := compactCoefficient κ₀ id (w' j) f.val
  let Q (x g : G) := ∫ k : Kc, w k * B f (x * (id k).val * g) ∂κ
  have hprod := complexAdjacentProductExpansion D μ d ((r : ℂ) / 2) s Φ ψ U.val l V' C Q
    (fun x g => by simpa only [Q, C, hCoeff, id_eq] using (hExpansion x g).1)
    (fun j => (hZ j).1) hE
  change complexUnequalIntegral gap D W (B f) s = N s * _
  rw [heq, zero_add, havg, hprod, cons_pairFactor, ReciprocalEntire.denominator_mul, mul_inv]
  dsimp only [N]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hZeq : (∫ g, Φ g.val * characterWeight d ((r : ℂ) / 2 + s) (determinant g) * C j g ∂μ) =
      Z j s * ((complexPairLFactor [d] (List.ofFn es)).denominator s)⁻¹ := by
    rw [(hZ j).2, mul_comm ((complexPairLFactor [d] (List.ofFn es)).denominator s),
      mul_assoc, mul_inv_cancel₀ hZne, mul_one]
  rw [hZeq]
  have hAeq := hτA j s ((le_max_left (τA j) _).trans_lt (hAll j))
  change complexEqualIntegral D U.val (V' j) ψ s = _ at hAeq
  rw [hAeq]
  ring

/-- The actual split Godement test with a compact-finite square factor has a normalized
ordinary integral of exponential strip growth, given the smaller equal-rank growth input. -/
def ComplexAdjacentJacquetStripGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData),
    ds.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a))
    (B : complexStandardKFinite (r + 1) (List.ofFn es) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner r (List.ofFn es) a B →
  ∀ (f : complexStandardKFinite (r + 1) (List.ofFn es))
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ (k.val⁻¹.val * X))) →
    (∀ V : complexWhittakerModel r (List.ofFn es) a,
      ∃ A : OrdinaryIntegralNormalization (complexEqualIntegral D U V (splitRowTransform a φ))
        (fun s => ((complexPairLFactor ds (List.ofFn es)).denominator s)⁻¹),
        HasStripExponentialGrowth A.value) →
    let W (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g 0
    ∃ R : OrdinaryIntegralNormalization (complexUnequalIntegral gap D W (B f))
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹),
      HasStripExponentialGrowth R.value

theorem complexAdjacentJacquetStripGrowth : ComplexAdjacentJacquetStripGrowthStatement (r := r) := by
  intro D hD κ hκf hκh a d ds es hds U B hB f Φ φ hΦ hA
  refine @adjacentJacquetNormalization r HasStripExponentialGrowth ?_ D hD κ hκf hκh a d
    ds es hds U B hB f Φ φ hΦ hA ?_
  · intro l c A Z hA hZ
    have hc : HasStripExponentialGrowth (fun _ => c) :=
      fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩
    exact hc.mul (finiteSumStripGrowth (fun j => (hA j).mul (hZ j)))
  · intro κ₀ hκ₀f hκ₀h w hw f₀ hf₀
    let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
    let Ψ := leftAverageInv κ₀ id continuous_id w hw Φ
    obtain ⟨τ, Z, hZd, hZg, hZ⟩ := ComplexSquareZeta.complexSquareZetaStripGrowth
      D.groupHaar κ₀ (fun i => (es i).mul d) Ψ f₀ hf₀
    exact ⟨τ, Z, hZd, hZg, fun s hs => (hZ s hs).2⟩

/-- For a standard square polynomial Gaussian, the continued split Godement test has a
polynomial ordinary normalization if the lower equal-rank normalizations for the transformed
row test are polynomial. -/
def ComplexAdjacentJacquetPolynomialStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData),
    ds.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a))
    (B : complexStandardKFinite (r + 1) (List.ofFn es) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner r (List.ofFn es) a B →
  ∀ (f : complexStandardKFinite (r + 1) (List.ofFn es))
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)) (p : MvPolynomial (Coordinates (r + 1) (r + 1)) ℂ),
    (Φ : Mat → ℂ) = squarePolynomialGaussian p →
    (∀ V : complexWhittakerModel r (List.ofFn es) a,
      ∃ (A : OrdinaryIntegralNormalization (complexEqualIntegral D U V (splitRowTransform a φ))
        (fun s => ((complexPairLFactor ds (List.ofFn es)).denominator s)⁻¹)) (P : Polynomial ℂ),
        A.value = P.eval) →
    let W (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g 0
    ∃ (N : OrdinaryIntegralNormalization (complexUnequalIntegral gap D W (B f))
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹)) (P : Polynomial ℂ),
      N.value = P.eval

theorem complexAdjacentJacquetPolynomial : ComplexAdjacentJacquetPolynomialStatement (r := r) := by
  intro D hD κ hκf hκh a d ds es hds U B hB f Φ φ p hΦ hA
  let R (F : ℂ → ℂ) : Prop := ∃ P : Polynomial ℂ, F = P.eval
  have hFin : ∀ (l : ℕ) (c : ℂ) (A Z : Fin l → ℂ → ℂ),
      (∀ j, R (A j)) → (∀ j, R (Z j)) → R (fun s => c * ∑ j, A j s * Z j s) := by
    intro l c A Z hA hZ
    choose P hP using hA
    choose Q hQ using hZ
    refine ⟨Polynomial.C c * ∑ j, P j * Q j, funext fun s => ?_⟩
    simp only [hP, hQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  refine @adjacentJacquetNormalization r R hFin D hD κ hκf hκh a d ds es hds U B hB f Φ φ
    (finiteDimensional_leftSquarePolynomialGaussian Φ p hΦ) hA ?_
  intro κ₀ hκ₀f hκ₀h w hw f₀ hf₀
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let Ψ := leftAverageInv κ₀ id continuous_id w hw Φ
  obtain ⟨p', _, hp'⟩ := leftAverageInv_squarePolynomialGaussian κ₀ id continuous_id w hw Φ p hΦ
  obtain ⟨τ, P, _, hP⟩ := ComplexSquareZeta.complexSquareZetaPolynomialGaussian (r + 1) (Nat.succ_pos r)
    D.groupHaar κ₀ (fun i => (es i).mul d) Ψ p' hp' f₀ hf₀
  exact ⟨τ, P.eval, P.differentiable, ⟨P, rfl⟩, fun s hs => (hP s hs).2⟩

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
