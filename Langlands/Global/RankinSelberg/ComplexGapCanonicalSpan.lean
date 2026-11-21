import Langlands.Global.RankinSelberg.ComplexAdjacentCanonicalChamber
import Langlands.Global.RankinSelberg.ComplexGapExactRestriction
import Langlands.Global.RankinSelberg.ComplexGapGaussianFactors
import Langlands.Global.RankinSelberg.ComplexLocalDualWhittakerGauge

/-! # Spanning by rotated Godement monomial values in a strict chamber -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapCanonicalSpan

open Langlands.Archimedean (unitaryCompact characterOfParams characterOfParams_exponent)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexSelfDualMeasure)
open ComplexAdjacentUnfolding (godementSection_finset_sum)
open ComplexCompactProfileFamily (characterList)
open ComplexGapExactRestriction (rotatedValue)
open ComplexGapRankCoordinates (tailWeyl_mul_self)
open ComplexGapWeylRestriction (tailWeyl)
open ComplexGodement (godementSection godementSectionIntegrand gaussianGodementSections addedCharacter
  retainedCharacters smallerWeights smallerExponents characterList_cons complexGodementGaussianSpanning
  complexGodementStandardConvergence)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial)
open ComplexGodementGaussianProduct (gaussianPolynomial_sum_monomials)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner
  continuedJacquet_mem_complexWhittakerModel complexJacquetSchwartzEvaluation)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable (t q : ℕ)
local notation "k" => t + 1
local notation "n" => t + 1 + q + 1
local notation "G" => Langlands.GeneralLinear (t + 1 + q + 1 + 1) ℂ
local notation "H" => Langlands.GeneralLinear (t + 1 + q + 1) ℂ
local notation "L" => Fin (t + 1 + q + 1 + 1) → ℤ
local notation "P" => Fin (t + 1 + q + 1 + 1) → ℂ
local notation "Tail" => Fin (t + 1 + q + 1) → ℂ
local notation "Poly" => MvPolynomial (Coordinates n (n + 1)) ℂ
local notation "Small[" l "," p "]" => Automorphic.complexStandardKFinite n (retainedCharacters l p)
local notation "Large[" l "," p "]" => Automorphic.complexStandardKFinite (n + 1) (characterList l p)
local notation "w" => tailWeyl k (q + 2)

private theorem tailWeyl_mem_unitary : (w : G) ∈ unitaryCompact ℂ (n + 1) := by
  unfold tailWeyl
  exact Langlands.Archimedean.ComplexBlockParabolicProof.blockDiagGL_mem_unitaryCompact'
    (Subgroup.one_mem _) (ComplexLocalDualWhittakerGauge.weylLong_mem_unitary (q + 2))

/-- The right-Weyl translates of the continued Godement monomial generators in the exact model. -/
def rotatedGaussianValues (l : L) (p : P) (a : ℂˣ) : Set (G → ℂ) :=
  {W | W ∈ complexWhittakerModel n (characterList l p) (-a) ∧
    ∃ (U : complexWhittakerModel (t + 1 + q) (retainedCharacters l p) (-a))
      (i : Coordinates n (n + 1) →₀ ℕ) (c : ℂ),
      W = rotatedValue t q a (addedCharacter l p)
        (operatorToEntry (gaussianPolynomial (MvPolynomial.monomial i c))) U.val 0}

/-- A sufficiently large adjoining exponent in the strict chamber gives spanning
by split Weyl-translated Godement monomials. -/
def ComplexGapCanonicalSpanStatement : Prop :=
  ∀ (l : L) (b : Tail), ∃ M : ℕ,
    ∀ (p : P), smallerExponents p = b → p ∈ chamber n →
      ((n : ℕ) : ℝ) + M ≤ (p 0 + ((((n : ℕ) : ℂ) + 1) / 2)).re →
    ∀ (a : ℂˣ) (F : Large[l, p]),
      continuedJacquet (complexSelfDualMeasure a) a l p F ∈ Submodule.span ℂ (rotatedGaussianValues t q l p a)

set_option maxHeartbeats 1600000 in
theorem complexGapCanonicalSpan : ComplexGapCanonicalSpanStatement t q := by
  classical
  intro l b
  let ν := complexGeneralLinearHaar n
  let ds := characterList (smallerWeights l) b
  have hds : ds.length = n := List.length_ofFn
  obtain ⟨M₁, hM₁⟩ := complexGodementGaussianSpanning (r := t + 1 + q) ν
    (fun i => characterOfParams (smallerWeights l i) (b i))
  obtain ⟨M₂, hM₂⟩ := complexJacquetSchwartzEvaluation (r := t + 1 + q) ν l b
  obtain ⟨M₃, hM₃⟩ := complexGodementStandardConvergence n (by omega) ds hds
  refine ⟨max M₁ (max M₂ M₃), fun p hb hp hd a F => ?_⟩
  have hEval := hM₂ p hb hp
  subst b
  let d := addedCharacter l p
  have hList : characterList l p = d :: ds := characterList_cons l p
  have hbound (j : ℕ) (hj : j ≤ max M₁ (max M₂ M₃)) :
      ((n : ℕ) : ℝ) + j ≤ (p 0 + ((((n : ℕ) : ℂ) + 1) / 2)).re := by
    have hcast : (j : ℝ) ≤ ((max M₁ (max M₂ M₃) : ℕ) : ℝ) := by exact_mod_cast hj
    exact (add_le_add (le_refl _) hcast).trans hd
  have hd₁ := hbound M₁ (le_max_left _ _)
  have hd₂ := hbound M₂ ((le_max_left _ _).trans (le_max_right _ _))
  have hd₃ := hbound M₃ ((le_max_right _ _).trans (le_max_right _ _))
  have hspan := hM₁ d (by simpa only [d, addedCharacter, characterOfParams_exponent] using hd₁)
  change Submodule.span ℂ (gaussianGodementSections ν d ds) =
    Langlands.Archimedean.kFiniteFunctions (Langlands.Archimedean.complexStandardModule (n + 1)
      (d :: ds)) (unitaryCompact ℂ (n + 1)) at hspan
  have hLarge : Submodule.span ℂ (gaussianGodementSections ν d ds) =
      Automorphic.complexStandardKFinite (n + 1) (characterList l p) :=
    hspan.trans (congrArg (Automorphic.complexStandardKFinite (n + 1)) hList).symm
  let μ := complexSelfDualMeasure a
  let J := continuedJacquet μ a l p
  let J₀ := continuedJacquet μ a (smallerWeights l) (smallerExponents p)
  let ρ := Whittaker.rightTranslation ℂ G w
  let Jr := ρ.comp J
  let S := Submodule.span ℂ (rotatedGaussianValues t q l p a)
  let gl (Q : Poly) (f : Small[l, p]) : Large[l, p] :=
    ⟨godementSection ν d (gaussianPolynomial Q) f.val,
      hLarge ▸ (Submodule.subset_span (s := gaussianGodementSections ν d ds) ⟨(Q, f), rfl⟩)⟩
  have hMonomial (i : Coordinates n (n + 1) →₀ ℕ) (c : ℂ) (f : Small[l, p]) :
      Jr (gl (MvPolynomial.monomial i c) f) ∈ S := by
    let Q : Poly := MvPolynomial.monomial i c
    let U : complexWhittakerModel (t + 1 + q) ds (-a) :=
      ⟨J₀ f, continuedJacquet_mem_complexWhittakerModel μ a (smallerWeights l) (smallerExponents p) f⟩
    have hW : Jr (gl Q f) = rotatedValue t q a d (operatorToEntry (gaussianPolynomial Q)) U.val 0 := by
      have he := hEval hd₂ μ a (gaussianPolynomial Q) f (gl Q f) rfl
      exact congrArg ρ he
    have hJ : J (gl Q f) ∈ complexWhittakerModel n (characterList l p) (-a) :=
      continuedJacquet_mem_complexWhittakerModel μ a l p (gl Q f)
    have hJr : Jr (gl Q f) ∈ complexWhittakerModel n (characterList l p) (-a) :=
      rightTranslation_mem_complexWhittakerModel hJ ⟨w, tailWeyl_mem_unitary t q⟩
    exact Submodule.subset_span ⟨hJr, U, i, c, hW⟩
  have hAll (Q : Poly) (f : Small[l, p]) : Jr (gl Q f) ∈ S := by
    let mon (i : Coordinates n (n + 1) →₀ ℕ) := MvPolynomial.monomial i (Q.coeff i)
    have hI (i : Coordinates n (n + 1) →₀ ℕ) (_ : i ∈ Q.support) (g : G) :
        Integrable (godementSectionIntegrand d (gaussianPolynomial (mon i)) f.val g) ν := by
      apply hM₃ d _ f.val f.2.1 _ g
      simpa only [d, addedCharacter, characterOfParams_exponent] using hd₃
    have hsum : gl Q f = ∑ i ∈ Q.support, gl (mon i) f := by
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      change godementSection ν d (gaussianPolynomial Q) f.val =
        ∑ i ∈ Q.support, godementSection ν d (gaussianPolynomial (mon i)) f.val
      rw [gaussianPolynomial_sum_monomials Q]
      exact godementSection_finset_sum Q.support ν d (fun i => gaussianPolynomial (mon i)) f.val hI
    rw [hsum, map_sum]
    exact S.sum_mem fun i _ => hMonomial i (Q.coeff i) f
  let A := (S.comap Jr).map (Automorphic.complexStandardKFinite (n + 1) (characterList l p)).subtype
  have hA : Submodule.span ℂ (gaussianGodementSections ν d ds) ≤ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨Q, f⟩, rfl⟩
    exact ⟨gl Q f, hAll Q f, rfl⟩
  have hAllRotated (v : Large[l, p]) : Jr v ∈ S := by
    have hv : v.val ∈ Submodule.span ℂ (gaussianGodementSections ν d ds) := hLarge.symm ▸ v.2
    obtain ⟨v₀, hv₀, he⟩ := hA hv
    exact (Subtype.ext he : v₀ = v) ▸ hv₀
  let u : unitaryCompact ℂ (n + 1) := ⟨w, tailWeyl_mem_unitary t q⟩
  let F' : Large[l, p] := ⟨ρ F.val,
    Langlands.Archimedean.rightTranslation_mem_kFiniteFunctions_complexStandardModule _ _ F.2 u.2⟩
  have hJ := (complexJacquetIntertwiner n μ a l p).2.2.2.1 u F F' rfl
  have hJr : Jr F' = J F := by
    change ρ (J F') = J F
    rw [hJ]
    funext g
    change J F (g * w * w) = J F g
    rw [mul_assoc, tailWeyl_mul_self, mul_one]
  exact hJr ▸ hAllRotated F'

end Langlands.Global.RankinSelbergGlobal.ComplexGapCanonicalSpan
