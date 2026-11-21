import Langlands.Global.RankinSelberg.ComplexGodementRecursionComparison
import Langlands.Global.RankinSelberg.ComplexJacquetCanonicalBounds
import Langlands.Global.RankinSelberg.ComplexJacquetGeneratorEvaluation

/-! # The quotient recursions span the canonical complex Jacquet values -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.GodementJacquet (complexJacquetRecursion)
open ArchimedeanLocal (complexSelfDualMeasure ComplexQuotientMeasureData)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile
  standardSection standardSection_compactRestriction)
open ComplexGodement (SmallerProfile HasFullRowRank smallerWeights smallerExponents addedCharacter
  complexGodementFiniteProfiles godementSection smallerSection)
open ComplexGodementAddedCharacter (continuedValue_eq_signed_recursion)
open ComplexGodementGeneratorFamily (generatorFamily)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ
local notation "Q" => Fin n → ℂ
local notation "L" => Fin n → ℤ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)

/-- The quotient recursion formed from a rectangular test and a canonical smaller coefficient. -/
def recursiveJacquetCoefficient (D : ComplexQuotientMeasureData r) (a : ℂˣ) (l : L) (p : Q)
    (Φ : 𝓢(Rect, ℂ)) (f : SmallerProfile l) : G → ℂ :=
  complexJacquetRecursion (-a) D (operatorToEntry Φ)
    (canonicalJacquetFamily (complexSelfDualMeasure a) a (smallerWeights l) f.val f.2 (smallerExponents p))
    (addedCharacter l p).character.toMonoidHom

/-- Every canonical Jacquet value of a larger standard vector lies in the span of the quotient
recursions with canonical smaller coefficients. -/
def ComplexJacquetRecursiveSpanStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (a : ℂˣ) (l : L) (p : Q),
    LinearMap.range (continuedJacquet (complexSelfDualMeasure a) a l p) ≤
      Submodule.span ℂ (range fun x : 𝓢(Rect, ℂ) × SmallerProfile l =>
        recursiveJacquetCoefficient D a l p x.1 x.2)

/-- Recursive coefficients obtained from compact tests supported on full-row-rank matrices. -/
def compactRecursiveGenerators (D : ComplexQuotientMeasureData r) (a : ℂˣ) (l : L) (p : Q) :
    Set (G → ℂ) :=
  {W | ∃ (Φ : 𝓢(Rect, ℂ)) (f : SmallerProfile l), HasCompactSupport Φ ∧
    (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧ W = recursiveJacquetCoefficient D a l p Φ f}

/-- The canonical range is spanned by the compact full-row-rank recursion generators. -/
def ComplexJacquetCompactRecursiveSpanStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (a : ℂˣ) (l : L) (p : Q),
    LinearMap.range (continuedJacquet (complexSelfDualMeasure a) a l p) ≤
      Submodule.span ℂ (compactRecursiveGenerators D a l p)

set_option maxHeartbeats 700000 in
theorem complexJacquetCompactRecursiveSpan : ComplexJacquetCompactRecursiveSpanStatement (r := r) := by
  intro D a l p W hW
  obtain ⟨v, rfl⟩ := hW
  let t := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := t.locallyCompactSpace
  let : SecondCountableTopology H := t.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.groupHaar
  let : D.groupHaar.IsMulRightInvariant := Archimedean.isMulRightInvariant_archimedeanGL ℂ m D.groupHaar
  let ν := D.groupHaar
  let μ := complexSelfDualMeasure a
  let φ := compactRestriction v.val
  obtain ⟨A, _, hvA, _, J, Φ, f, htest, hspan⟩ :=
    complexGodementFiniteProfiles ν l φ (compactRestriction_isCompactProfile v.2)
  let F (j : J) (q : Q) : Std[l, q] :=
    ⟨godementSection ν (addedCharacter l q) (Φ j) (smallerSection q (f j)),
      godementSection_mem_standardKFinite ν l (Φ j)
        (htest j).1 (htest j).2.1 (htest j).2.2 (f j) q⟩
  let C := compactRestriction.comp ((Std[l, p]).subtype)
  have hC : Function.Injective C := by
    intro v₁ v₂ h
    apply Subtype.ext
    exact (standardSection_compactRestriction v₁.2).symm.trans
      ((congrArg (standardSection p) h).trans (standardSection_compactRestriction v₂.2))
  let V := Submodule.span ℂ (range fun j => F j p)
  have hCV : V.map C = A := by
    dsimp only [V]
    rw [Submodule.map_span, ← Set.range_comp]
    exact hspan p
  have hvV : v ∈ V := by
    have hc : C v ∈ V.map C := hCV.symm ▸ hvA
    obtain ⟨v', hv', he⟩ := hc
    exact (hC he) ▸ hv'
  let T := continuedJacquet μ a l p
  let R := Submodule.span ℂ (compactRecursiveGenerators D a l p)
  change T v ∈ R
  have hTV : V.map T ≤ R := by
    dsimp only [V]
    rw [Submodule.map_span, ← Set.range_comp]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    let d := characterOfParams (l 0) 0
    let S : ℂ := d.character ((-1 : ℂˣ) ^ m)
    have hW₁ := complexJacquetCanonicalBounds μ a (smallerWeights l) (f j).val (f j).2 (smallerExponents p)
    have he : T (F j p) = S • recursiveJacquetCoefficient D a l p (Φ j) (f j) := by
      funext g
      calc
        T (F j p) g = generatorFamily ν μ a l (Φ j)
            (canonicalJacquetFamily μ a (smallerWeights l) (f j).val (f j).2) p g :=
          congrFun (complexJacquetGeneratorEvaluation ν μ a l (Φ j)
            (htest j).1 (htest j).2.1 (htest j).2.2 (f j) p) g
        _ = (S • recursiveJacquetCoefficient D a l p (Φ j) (f j)) g := by
          have h := continuedValue_eq_signed_recursion a D d (operatorToEntry (Φ j))
            hW₁.1 hW₁.2.1 hW₁.2.2 g (p 0)
          simpa only [generatorFamily, recursiveJacquetCoefficient, Pi.smul_apply, smul_eq_mul,
            μ, ν, d, S, addedCharacter, characterOfParams_exponent, characterOfParams_weight, zero_add] using h
    change T (F j p) ∈ R
    rw [he]
    exact R.smul_mem S (Submodule.subset_span ⟨Φ j, f j, (htest j).1, (htest j).2.1, rfl⟩)
  exact hTV (Submodule.mem_map_of_mem hvV)

theorem complexJacquetRecursiveSpan : ComplexJacquetRecursiveSpanStatement (r := r) := by
  intro D a l p
  refine (complexJacquetCompactRecursiveSpan D a l p).trans (Submodule.span_mono ?_)
  rintro _ ⟨Φ, f, _, _, rfl⟩
  exact ⟨⟨Φ, f⟩, rfl⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
