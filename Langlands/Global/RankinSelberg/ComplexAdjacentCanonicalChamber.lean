import Langlands.Global.RankinSelberg.ComplexAdjacentSplitEquation
import Langlands.Global.RankinSelberg.ComplexGodementGaussianSpanning
import Langlands.Global.RankinSelberg.ComplexGodementSplitSpanning
import Langlands.Global.RankinSelberg.ComplexJacquetIntertwiner
import Langlands.Global.RankinSelberg.ComplexJacquetSchwartzEvaluation
import Langlands.Global.RankinSelberg.ComplexLocalDualConvergence
import Langlands.Global.RankinSelberg.ComplexUnequalNormalizedSpan

/-! # The normalized adjacent-rank equation in a strong chamber -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams characterOfParams_exponent unitaryCompact)
open Langlands.Archimedean.ComplexDuality (unitaryHaar)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (godementSection godementSectionIntegrand addedCharacter retainedCharacters
  smallerWeights smallerExponents characterList_cons gaussianGodementSections
  complexGodementGaussianSpanning complexGodementStandardConvergence)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial)
open ComplexGodementGaussianProduct (complexGodementSplitSpanning)
open ComplexGodementColumnProduct (columnProduct)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner
  continuedJacquet_mem_complexWhittakerModel complexJacquetSchwartzEvaluation)
open ComplexLocalWhittakerGrowth (complexWhittakerCompactProjection)
open ComplexJacquet (HasComplexPairNormalizedGrowth)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => (r + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "P" => Fin (r + 1 + 1) → ℂ
local notation "L" => Fin (r + 1 + 1) → ℤ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Poly" => MvPolynomial (Coordinates (r + 1) (r + 1 + 1)) ℂ
local notation "Small[" l "," p "]" => Automorphic.complexStandardKFinite m (retainedCharacters l p)
local notation "Large[" l "," p "]" => Automorphic.complexStandardKFinite (m + 1) (characterList l p)
local notation "gap" => Nat.lt_succ_self r

/-- The lower equal-rank convergence and normalized equation used by the adjacent unfolding. -/
def HasAdjacentLowerEqualInputs (D : ComplexQuotientMeasureData r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) : Prop :=
  ∀ (U : complexWhittakerModel r ds (-a)) (V : H → ℂ), V ∈ complexWhittakerModel r es a →
  ∀ φ : 𝓢(Vec, ℂ),
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand U.val V (splitRowTransform a φ) s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction m U.val)
        (ArchimedeanLocal.dualFunction m V) φ s) D.measure) ∧
    HasComplexPairNormalization ds es (-a) (complexCentralSign es ^ r)
      (complexEqualIntegral D U.val V (splitRowTransform a φ))
      (complexEqualDualIntegral (-a) D U.val V (splitRowTransform a φ))

/-- The lower equal-rank convergence and strip-growing normalized equation used by the adjacent unfolding. -/
def HasAdjacentLowerEqualGrowthInputs (D : ComplexQuotientMeasureData r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) : Prop :=
  ∀ (U : complexWhittakerModel r ds (-a)) (V : H → ℂ), V ∈ complexWhittakerModel r es a →
  ∀ φ : 𝓢(Vec, ℂ),
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand U.val V (splitRowTransform a φ) s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction m U.val)
        (ArchimedeanLocal.dualFunction m V) φ s) D.measure) ∧
    HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ r)
      (complexEqualIntegral D U.val V (splitRowTransform a φ))
      (complexEqualDualIntegral (-a) D U.val V (splitRowTransform a φ))

/-- The Godement section is additive in an integrable finite family of Schwartz tests. -/
theorem godementSection_finset_sum {I : Type*} (T : Finset I) (ν : Measure H)
    (d : ComplexCharacterData) (Φ : I → 𝓢(Rect, ℂ)) (f : H → ℂ)
    (hI : ∀ i ∈ T, ∀ g, Integrable (godementSectionIntegrand d (Φ i) f g) ν) :
    godementSection ν d (show 𝓢(Rect, ℂ) from ∑ i ∈ T, Φ i) f =
      ∑ i ∈ T, godementSection ν d (Φ i) f := by
  funext g
  have h : godementSectionIntegrand d (show 𝓢(Rect, ℂ) from ∑ i ∈ T, Φ i) f g =
      fun h => ∑ i ∈ T, godementSectionIntegrand d (Φ i) f g h := by
    funext h
    simp only [godementSectionIntegrand, sum_apply, Finset.sum_mul]
  simp only [Finset.sum_apply, godementSection, h, integral_finsetSum T (fun i hi => hI i hi g),
    Finset.mul_sum]

/-- The canonical larger Jacquet values in a sufficient strict chamber satisfy the adjacent-rank
normalized equation against every smaller intertwiner value, given the lower equal-rank inputs. -/
def ComplexAdjacentCanonicalChamberStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (l : L) (q : Fin m → ℂ),
    ∃ M : ℕ, ∀ (p : P), smallerExponents p = q → p ∈ chamber (r + 1) →
    (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
    ∀ (a : ℂˣ) (es : List ComplexCharacterData), es.length = m →
    HasAdjacentLowerEqualInputs D (retainedCharacters l p) es a →
    ∀ (B : Automorphic.complexStandardKFinite m es →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner r es a B →
    ∀ (v : Automorphic.complexStandardKFinite m es) (F : Large[l, p]),
      let W := continuedJacquet (complexSelfDualMeasure a) a l p F
      HasComplexPairNormalization (characterList l p) es (-a) (complexCentralSign es ^ (r + 1))
        (complexUnequalIntegral gap D W (B v)) (complexUnequalDualIntegral gap (-a) D W (B v))

private def adjacentSplitValues (D : ComplexQuotientMeasureData r) (l : L) (p : P) (a : ℂˣ) : Set (G → ℂ) :=
  {W | W ∈ complexWhittakerModel (r + 1) (characterList l p) (-a) ∧
    ∃ (U : complexWhittakerModel r (retainedCharacters l p) (-a))
      (A : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ)) (φ : 𝓢(Vec, ℂ)),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ m =>
        fun X => A (k.val⁻¹.val * X))) ∧
      W = fun g => continuedValue D.groupHaar (complexSelfDualMeasure a) (addedCharacter l p) a
        (operatorToEntry (columnProduct A φ)) U.val g 0}

private def AdjacentCanonicalSplitSpan : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (l : L) (q : Fin m → ℂ),
    ∃ M : ℕ, ∀ (p : P), smallerExponents p = q → p ∈ chamber (r + 1) →
    (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
    ∀ (a : ℂˣ) (F : Large[l, p]),
      continuedJacquet (complexSelfDualMeasure a) a l p F ∈ Submodule.span ℂ (adjacentSplitValues D l p a)

set_option maxHeartbeats 1600000 in
private theorem adjacentCanonicalSplitSpan : AdjacentCanonicalSplitSpan (r := r) := by
  classical
  intro D _ l q
  let ν := D.groupHaar
  let : ν.IsHaarMeasure := D.groupHaar_isHaar
  let : ν.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D
  let eH := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := eH.locallyCompactSpace
  let : SecondCountableTopology H := eH.secondCountableTopology
  let ds := characterList (smallerWeights l) q
  have hds : ds.length = m := List.length_ofFn
  obtain ⟨M₁, hM₁⟩ := complexGodementGaussianSpanning (r := r) ν
    (fun i => characterOfParams (smallerWeights l i) (q i))
  obtain ⟨M₂, hM₂⟩ := complexJacquetSchwartzEvaluation (r := r) ν l q
  obtain ⟨M₃, hM₃⟩ := complexGodementStandardConvergence m (Nat.succ_pos r) ds hds
  refine ⟨max M₁ (max M₂ M₃), fun p hq hp hd a F => ?_⟩
  have hEval := hM₂ p hq hp
  subst q
  let d := addedCharacter l p
  have hList : characterList l p = d :: ds := characterList_cons l p
  have hbound (j : ℕ) (hj : j ≤ max M₁ (max M₂ M₃)) :
      (m : ℝ) + j ≤ (p 0 + (((m : ℂ) + 1) / 2)).re := by
    have hcast : (j : ℝ) ≤ ((max M₁ (max M₂ M₃) : ℕ) : ℝ) := by exact_mod_cast hj
    exact (add_le_add (le_refl _) hcast).trans hd
  have hd₁ := hbound M₁ (le_max_left _ _)
  have hd₂ := hbound M₂ ((le_max_left _ _).trans (le_max_right _ _))
  have hd₃ := hbound M₃ ((le_max_right _ _).trans (le_max_right _ _))
  have hspan := hM₁ d (by simpa only [d, addedCharacter, characterOfParams_exponent] using hd₁)
  change Submodule.span ℂ (gaussianGodementSections ν d ds) =
    Langlands.Archimedean.kFiniteFunctions (Langlands.Archimedean.complexStandardModule (m + 1)
      (d :: ds)) (unitaryCompact ℂ (m + 1)) at hspan
  have hLarge : Submodule.span ℂ (gaussianGodementSections ν d ds) =
      Automorphic.complexStandardKFinite (m + 1) (characterList l p) :=
    hspan.trans (congrArg (Automorphic.complexStandardKFinite (m + 1)) hList).symm
  let μ := complexSelfDualMeasure a
  let J := continuedJacquet μ a l p
  let J₀ := continuedJacquet μ a (smallerWeights l) (smallerExponents p)
  let S := Submodule.span ℂ (adjacentSplitValues D l p a)
  let gl (Q : Poly) (f : Small[l, p]) : Large[l, p] :=
    ⟨godementSection ν d (gaussianPolynomial Q) f.val,
      hLarge ▸ (Submodule.subset_span (s := gaussianGodementSections ν d ds) ⟨(Q, f), rfl⟩)⟩
  have hMonomial (Q : Poly) (f : Small[l, p]) (A : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ))
      (φ : 𝓢(Vec, ℂ)) (hQ : gaussianPolynomial Q = columnProduct A φ)
      (hA : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ m =>
        fun X => A (k.val⁻¹.val * X)))) :
      J (gl Q f) ∈ S := by
    let U : complexWhittakerModel r ds (-a) :=
      ⟨J₀ f, continuedJacquet_mem_complexWhittakerModel μ a
        (smallerWeights l) (smallerExponents p) f⟩
    have hW : J (gl Q f) = fun g => continuedValue ν μ d a (operatorToEntry (columnProduct A φ)) U.val g 0 := by
      have he := hEval hd₂ μ a (gaussianPolynomial Q) f (gl Q f) rfl
      rw [hQ] at he
      exact he
    have hJG : J (gl Q f) ∈ complexWhittakerModel (r + 1) (characterList l p) (-a) :=
      continuedJacquet_mem_complexWhittakerModel μ a l p (gl Q f)
    apply Submodule.subset_span
    exact ⟨hJG, U, A, φ, hA, hW⟩
  have hAll (Q : Poly) (f : Small[l, p]) : J (gl Q f) ∈ S := by
    obtain ⟨hExpand, hQ⟩ := complexGodementSplitSpanning m Q
    let pol (u : Coordinates m (m + 1) →₀ ℕ) := MvPolynomial.monomial u (Q.coeff u)
    have hI (u : Coordinates m (m + 1) →₀ ℕ) (_ : u ∈ Q.support) (g : G) :
        Integrable (godementSectionIntegrand d (gaussianPolynomial (pol u)) f.val g) ν := by
      rw [Measure.isMulLeftInvariant_eq_smul ν (complexGeneralLinearHaar m)]
      have hs : (m : ℝ) + M₃ ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re := by
        simpa only [d, addedCharacter, characterOfParams_exponent] using hd₃
      exact (hM₃ d (gaussianPolynomial (pol u)) f.val f.2.1 hs g).smul_measure_nnreal
    have hsum : gl Q f = ∑ u ∈ Q.support, gl (pol u) f := by
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      change godementSection ν d (gaussianPolynomial Q) f.val =
        ∑ u ∈ Q.support, godementSection ν d (gaussianPolynomial (pol u)) f.val
      rw [hExpand]
      exact godementSection_finset_sum Q.support ν d
        (fun u => gaussianPolynomial (pol u)) f.val hI
    rw [hsum, map_sum]
    apply S.sum_mem
    intro u hu
    obtain ⟨A, φ, hA, hfin⟩ := hQ u hu
    exact hMonomial (pol u) f A φ hA hfin
  let A := (S.comap J).map (Automorphic.complexStandardKFinite (m + 1) (characterList l p)).subtype
  have hA : Submodule.span ℂ (gaussianGodementSections ν d ds) ≤ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨Q, f⟩, rfl⟩
    exact ⟨gl Q f, hAll Q f, rfl⟩
  have hFA : F.val ∈ A := hA (hLarge.symm ▸ F.2)
  obtain ⟨v₀, hv₀, he⟩ := hFA
  have he' : v₀ = F := Subtype.ext he
  exact he' ▸ hv₀

theorem complexAdjacentCanonicalChamber : ComplexAdjacentCanonicalChamberStatement (r := r) := by
  intro D _ l q
  obtain ⟨M, hM⟩ := adjacentCanonicalSplitSpan D l q
  refine ⟨M, fun p hp₁ hp₂ hp₃ a es hes hEqual B hB v F => ?_⟩
  let S := complexUnequalNormalizedSpace gap D (characterList l p) es (-a) (B v)
  have hV : B v ∈ complexWhittakerModel r es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  let κ := unitaryHaar m
  have hProjection (w : unitaryCompact ℂ m → ℂ) (hw : Continuous w)
      (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : unitaryCompact ℂ m =>
        fun k => w (h⁻¹ * k)))) (g : H) :=
    complexWhittakerCompactProjection (r := r) es a κ (inferInstanceAs κ.IsHaarMeasure)
      ⟨w, hw⟩ hfin B hB v g
  have hS : Submodule.span ℂ (adjacentSplitValues D l p a) ≤ S := by
    apply Submodule.span_le.mpr
    rintro W ⟨hWmodel, U, A, φ, hA, hW⟩
    let d := addedCharacter l p
    let ds := retainedCharacters l p
    have hds : ds.length = m := List.length_ofFn
    have hNorm := complexAdjacentSplitEquation (r := r) D κ a d A φ hA
      ds es hds hes U v B hB hProjection (fun V hV' => hEqual U V hV' φ)
    change HasComplexPairNormalization (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (complexUnequalIntegral gap D _ (B v)) (complexUnequalDualIntegral gap (-a) D _ (B v)) at hNorm
    rw [← hW, ← characterList_cons l p] at hNorm
    have hConv := complexLocalUnequalConvergence gap (characterList l p) es (-a) D
      ⟨W, hWmodel⟩ ⟨B v, by simpa only [neg_neg] using hV⟩
    exact (complexUnequalNormalizedSpan (r + 1) r gap D _ es (-a) _ (B v)).2 ⟨hConv, hNorm⟩
  exact ((complexUnequalNormalizedSpan (r + 1) r gap D _ es (-a) _ (B v)).1
    (hS (hM p hp₁ hp₂ hp₃ a F))).2

/-- The adjacent canonical chamber equation with exponential strip growth in the lower and upper pairs. -/
def ComplexAdjacentCanonicalChamberGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (l : L) (q : Fin m → ℂ),
    ∃ M : ℕ, ∀ (p : P), smallerExponents p = q → p ∈ chamber (r + 1) →
    (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
    ∀ (a : ℂˣ) (es : List ComplexCharacterData), es.length = m →
    HasAdjacentLowerEqualGrowthInputs D (retainedCharacters l p) es a →
    ∀ (B : Automorphic.complexStandardKFinite m es →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner r es a B →
    ∀ (v : Automorphic.complexStandardKFinite m es) (F : Large[l, p]),
      let W := continuedJacquet (complexSelfDualMeasure a) a l p F
      HasComplexPairNormalizedGrowth (characterList l p) es (-a) (complexCentralSign es ^ (r + 1))
        (complexUnequalIntegral gap D W (B v)) (complexUnequalDualIntegral gap (-a) D W (B v))

theorem complexAdjacentCanonicalChamberGrowth : ComplexAdjacentCanonicalChamberGrowthStatement (r := r) := by
  intro D _ l q
  obtain ⟨M, hM⟩ := adjacentCanonicalSplitSpan D l q
  refine ⟨M, fun p hp₁ hp₂ hp₃ a es hes hEqual B hB v F => ?_⟩
  let S := complexUnequalNormalizedGrowthSpace gap D (characterList l p) es (-a) (B v)
  have hV : B v ∈ complexWhittakerModel r es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  let κ := unitaryHaar m
  have hProjection (w : unitaryCompact ℂ m → ℂ) (hw : Continuous w)
      (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : unitaryCompact ℂ m =>
        fun k => w (h⁻¹ * k)))) (g : H) :=
    complexWhittakerCompactProjection (r := r) es a κ (inferInstanceAs κ.IsHaarMeasure)
      ⟨w, hw⟩ hfin B hB v g
  have hS : Submodule.span ℂ (adjacentSplitValues D l p a) ≤ S := by
    apply Submodule.span_le.mpr
    rintro W ⟨hWmodel, U, A, φ, hA, hW⟩
    let d := addedCharacter l p
    let ds := retainedCharacters l p
    have hds : ds.length = m := List.length_ofFn
    have hNorm := complexAdjacentSplitGrowth (r := r) D κ a d A φ hA
      ds es hds hes U v B hB hProjection (fun V hV' => hEqual U V hV' φ)
    change HasComplexPairNormalizedGrowth (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (complexUnequalIntegral gap D _ (B v)) (complexUnequalDualIntegral gap (-a) D _ (B v)) at hNorm
    rw [← hW, ← characterList_cons l p] at hNorm
    have hConv := complexLocalUnequalConvergence gap (characterList l p) es (-a) D
      ⟨W, hWmodel⟩ ⟨B v, by simpa only [neg_neg] using hV⟩
    exact (complexUnequalNormalizedGrowthSpan (r + 1) r gap D _ es (-a) _ (B v)).2 ⟨hConv, hNorm⟩
  exact ((complexUnequalNormalizedGrowthSpan (r + 1) r gap D _ es (-a) _ (B v)).1
    (hS (hM p hp₁ hp₂ hp₃ a F))).2

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
