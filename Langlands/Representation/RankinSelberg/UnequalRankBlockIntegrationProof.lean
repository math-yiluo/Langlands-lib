import Langlands.Representation.RankinSelberg.UnequalRankBlockMatrix
import Langlands.Representation.RankinSelberg.UnequalRankBlockIntegrationStatement
import Langlands.HarmonicAnalysis.CompactCosetExpansion
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Block matrix and integration helpers for unequal-rank JPSS integrals

Worker 180 authored the nine helper proofs in the adjacent-block draft.
Worker 52 extracted them into this focused module and assembled the exact
published aggregate. The representation carrier stays algebraic, support
remains an explicit premise, and every measure is the supplied measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.AdjacentBlockReduction

open MeasureTheory HarmonicAnalysis

section CoefficientFiber

open Whittaker

universe uX uP uG uV

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {P : Type uP}
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Integrating a uniformly compactly supported family of right translates
along a continuous group map is represented by a coefficient in the same model.
The representation carrier remains purely algebraic. -/
theorem exists_coefficient_fiber_integral (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {N : Subgroup G} {θ : N →* ℂˣ} (ℓ : functionals N θ ρ)
    (U : X → G) (hU : Continuous U) (B : P → G)
    (f : (coefficientModel ρ ℓ).toSubmodule)
    (hc : HasCompactSupport (fun x p => f.val.val (B p * U x))) :
    ∃ f₀ : (coefficientModel ρ ℓ).toSubmodule, ∀ p,
      Integrable (fun x => f.val.val (B p * U x)) μ ∧
      f₀.val.val (B p) = ∫ x, f.val.val (B p * U x) ∂μ := by
  classical
  obtain ⟨v, rfl⟩ := modelMap_surjective ρ ℓ f
  let H : X → P → ℂ := fun x p => ℓ.val (ρ (B p * U x) v)
  have hH : IsLocallyConstant H := by
    have h := ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous hU).comp
      (fun w p => ℓ.val (ρ (B p) w))
    simpa only [H, Function.comp_def, map_mul, Module.End.mul_apply] using h
  obtain ⟨m, φ, x, he⟩ :=
    HarmonicAnalysis.exists_finite_schwartz_expansion H hH hc
  let c : Fin m → ℂ := fun i => ∫ y, φ i y ∂μ
  let w : V := ∑ i : Fin m, c i • ρ (U (x i)) v
  refine ⟨modelMap ρ ℓ w, ?_⟩
  intro p
  have hi (i : Fin m) : Integrable (fun y => φ i y * H (x i) p) μ :=
    ((φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport).mul_const _
  have hfun : (fun y => H y p) = fun y => ∑ i : Fin m, φ i y * H (x i) p :=
    funext (he p)
  change Integrable (fun y => H y p) μ ∧ ℓ.val (ρ (B p) w) = ∫ y, H y p ∂μ
  constructor
  · rw [hfun]
    exact integrable_finsetSum _ (fun i _ => hi i)
  · rw [hfun, integral_finsetSum _ (fun i _ => hi i)]
    simp only [w, map_sum, map_smul, smul_eq_mul, integral_mul_const]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, H, map_mul, Module.End.mul_apply]

end CoefficientFiber

section LastRowCoefficient

open Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem unequalRankMatrix_snoc {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F) (x : Fin (n + 1) → F) :
    unequalRankMatrix (j + 1) k g (Fin.snoc Y x) =
      unequalRankMatrix (j + 1) k g (Fin.snoc Y 0) *
        rectangularUnipotent (j + 1) k (Fin.snoc 0 x) := by
  have he : (Fin.snoc Y x : Matrix (Fin (j + 1)) (Fin (n + 1)) F) =
      Fin.snoc Y 0 + Fin.snoc 0 x := by
    funext a b
    induction a using Fin.lastCases <;> simp [Fin.snoc]
  rw [he]
  unfold unequalRankMatrix
  rw [rectangularUnipotent_add, mul_assoc]

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem blockMatrixAt_entry {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F) (a b : Fin (r + 1)) :
    blockMatrixAt j k hr g Y a b =
      (if ha : a.val < n + 1 then
        if hb : b.val < n + 1 then g ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
       else if a = b then 1 else 0) +
      (if ha : n + 1 ≤ a.val ∧ a.val < n + 1 + j then
        if hb : b.val < n + 1 then Y ⟨a.val - (n + 1), by omega⟩ ⟨b.val, hb⟩ else 0
       else 0) := by
  subst r
  change (unequalRankMatrix j k g Y).val a b = _
  rw [unequalRankMatrix_val, Matrix.add_apply, appendIdentity_entry]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- A zero last rectangular row is the neighboring block matrix. -/
theorem blockMatrixAt_snoc_zero {n r : ℕ} (j k : ℕ)
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F) :
    blockMatrixAt (j + 1) k h₁ g (Fin.snoc Y 0) =
      blockMatrixAt j (k + 1) h₂ g Y := by
  apply Units.ext
  ext a b
  simp only [blockMatrixAt_entry]
  congr 1
  by_cases ha : n + 1 ≤ a.val ∧ a.val < n + 1 + j
  · have ha' : n + 1 ≤ a.val ∧ a.val < n + 1 + (j + 1) := by omega
    simp only [dite_eq_left ha, dite_eq_left ha']
    split_ifs with hb
    · have hi : (⟨a.val - (n + 1), by omega⟩ : Fin (j + 1)) =
          (⟨a.val - (n + 1), by omega⟩ : Fin j).castSucc := by rfl
      rw [hi]
      exact congrFun (@Fin.snoc_castSucc j (fun _ => Fin (n + 1) → F)
        0 (fun a b => Y a b) ⟨a.val - (n + 1), by omega⟩) ⟨b.val, hb⟩
    · rfl
  · simp only [dite_eq_right ha]
    split_ifs with ha' hb
    · have hi : (⟨a.val - (n + 1), by omega⟩ : Fin (j + 1)) = Fin.last j := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [hi]
      simp
    · rfl
    · rfl


/-- The last-row right translation depends continuously on the row. -/
theorem continuous_lastRowUnipotent (n j k : ℕ) :
    Continuous (fun x : Fin (n + 1) → F =>
      rectangularUnipotent (j + 1) k (Fin.snoc 0 x)) := by
  apply (continuous_rectangularUnipotent (j + 1) k).comp
  apply continuous_pi
  intro a
  induction a using Fin.lastCases with
  | last =>
    convert (continuous_id : Continuous (fun x : Fin (n + 1) → F => x)) using 1
    ext x b
    simp [Fin.snoc]
  | cast a => simpa [Fin.snoc] using (continuous_const : Continuous (fun _ : Fin (n + 1) → F => (0 : Fin (n + 1) → F)))


end LastRowCoefficient

section RowMeasures

universe uF

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

/-- Splitting off the last rectangular row preserves the supplied product Haar
measure, including when the earlier row space has dimension zero. -/
theorem rectangular_lastRow_measurePreserving (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (j t : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => Fin t → F) (Fin.last j))
      (rectangularMeasure ν (j + 1) t)
      ((rowMeasure ν t).prod (rectangularMeasure ν j t)) := by
  exact measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => rowMeasure ν t)
    (Fin.last j)

/-- Genuine Fubini splits the last row after the preceding rows; absolute
integrability is retained as an explicit hypothesis. -/
theorem rectangular_integral_lastRow (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (j t : ℕ)
    (f : Matrix (Fin (j + 1)) (Fin t) F → ℂ)
    (hf : Integrable f (rectangularMeasure ν (j + 1) t)) :
    (∫ X, f X ∂rectangularMeasure ν (j + 1) t) =
      ∫ Y, ∫ x, f (Fin.snoc Y x) ∂rowMeasure ν t ∂rectangularMeasure ν j t := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (j + 1) => Fin t → F) (Fin.last j)
  have hm := (rectangular_lastRow_measurePreserving ν j t).symm
  have hi := hm.integrable_comp_of_integrable hf
  calc
    _ = ∫ p, f (e.symm p)
        ∂(rowMeasure ν t).prod (rectangularMeasure ν j t) :=
      (hm.integral_comp' f).symm
    _ = ∫ Y, ∫ x, f (e.symm (x, Y))
        ∂rowMeasure ν t ∂rectangularMeasure ν j t :=
      integral_prod_symm _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with Y
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      exact Fin.insertNth_last' x Y

end RowMeasures

section AdjacentIntegral

open Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] [MeasurableSpace F] [BorelSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [T2Space F] [BorelSpace F] in
/-- Smoothness and one uniform support set give genuine integrability in all
rectangular variables, independently of quotient convergence. -/
theorem blockCoefficient_integrable (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (n j k : ℕ)
    [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + (j + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (C : Set (Matrix (Fin j) (Fin (n + 1)) F)) (hC : IsCompact C)
    (hs : ∀ g X, f.val.val (unequalRankMatrix j k g X) ≠ 0 → X ∈ C)
    (g : Langlands.GeneralLinear (n + 1) F) :
    Integrable (fun X => f.val.val (unequalRankMatrix j k g X))
      (rectangularMeasure ν j (n + 1)) := by
  let : IsFiniteMeasureOnCompacts (rectangularMeasure ν j (n + 1)) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts
      (Measure.pi (fun _ : Fin j => rowMeasure ν (n + 1))))
  have hc : HasCompactSupport
      (fun X (g : Langlands.GeneralLinear (n + 1) F) =>
        f.val.val (appendIdentity n (j + k + 1) g * rectangularUnipotent j k X)) := by
    apply HasCompactSupport.intro hC
    intro X hX
    funext g
    exact not_ne_iff.mp (fun hn => hX (hs g X hn))
  obtain ⟨f₀, hf₀⟩ := exists_coefficient_fiber_integral
    (rectangularMeasure ν j (n + 1)) π hπ ℓ
    (rectangularUnipotent j k) (continuous_rectangularUnipotent j k)
    (appendIdentity n (j + k + 1)) f hc
  exact (hf₀ g).1


omit [T2Space F] [BorelSpace F] [IsTopologicalRing F] in
/-- Express the existing fixed-rank integral using transported actual matrices
and representatives of the same quotient points. -/
theorem unequalRankIntegralAt_eq_outer {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (f : WhittakerFunctions ψ r) (f' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ ν f f' s =
      ∫ q, ((∫ X, f.val (blockMatrixAt j k hr q.out X) ∂ν) * f'.val q.out *
        determinantWeight abv q.out (s - ((j + k + 1 : ℕ) : ℂ) / 2)) ∂μ := by
  subst r
  change (∫ q, ∫ X, unequalRankIntegrand ψ abv j k f f' s X q ∂ν ∂μ) = _
  apply integral_congr_ae
  filter_upwards [] with q
  have he (X) : unequalRankIntegrand ψ abv j k f f' s X q =
      f.val (blockMatrixAt j k rfl q.out X) * f'.val q.out *
        determinantWeight abv q.out (s - ((j + k + 1 : ℕ) : ℂ) / 2) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp_rw [he, integral_mul_const]


end AdjacentIntegral

/-- The complete published package, with all nine universal helper telescopes
and their independent carrier universes. -/
theorem unequalRankBlockIntegration.{uX, uP, uG, uF, uV} :
    UnequalRankBlockIntegrationStatement.{uX, uP, uG, uF, uV} :=
  ⟨@exists_coefficient_fiber_integral.{uX, uP, uG, uV},
   @unequalRankMatrix_snoc.{uF},
   @blockMatrixAt_entry.{uF},
   @blockMatrixAt_snoc_zero.{uF},
   @continuous_lastRowUnipotent.{uF},
   @rectangular_lastRow_measurePreserving.{uF},
   @rectangular_integral_lastRow.{uF},
   @blockCoefficient_integrable.{uF, uV},
   @unequalRankIntegralAt_eq_outer.{uF}⟩

end Langlands.RankinSelberg.AdjacentBlockReduction
