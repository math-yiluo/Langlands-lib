import Langlands.Global.RankinSelberg.ComplexGodementContinuedModel
import Langlands.Global.RankinSelberg.ComplexGodementHalfPlane
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin
import Langlands.Representation.Archimedean.ComplexStandardIrreducibilityInStages

/-! # Left covariance of a continued Godement family with unlinked retained data -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (addedCharacter retainedCharacters characterList_cons smallerWeights smallerExponents
  shiftedCharacter shiftedCharacter_exponent translateTest)
open ComplexGodementAddedCharacter (continuedValue continuedValue_eq_shiftedCharacter)
open ComplexGodementContinuedModel (complexGodementContinuedModel)
open ComplexGodementGeneratorFamily (differentiable_generatorValue)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)
open ComplexJacquetMultiplicityOne (exists_characterList)
open ComplexUnequalFamily (HasLeftCharacter)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 1 + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ

private theorem not_linked_of_im_ne {x y : ComplexCharacterData} (h : x.exponent.im ≠ y.exponent.im) :
    ¬ IsComplexLinked x y := by
  rintro ⟨p, q, hpq, hp, hq⟩
  have hx : (((x.weight : ℂ) / 2)).im = 0 := by simp
  have hy : (((y.weight : ℂ) / 2)).im = 0 := by simp
  have he := congrArg Complex.im hp
  simp only [Complex.sub_im, Complex.add_im, hx, hy, add_zero, Complex.intCast_im] at he
  exact h (sub_eq_zero.mp he)

/-- The continued Godement value with fixed unlinked retained data and finite right unitary
translate span of the test is pointwise entire in the adjoining exponent and satisfies the
larger left Whittaker law at every exponent. -/
def ComplexGodementUnlinkedFamilyStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData), ds.length = m → IsComplexUnlinked ds →
    ∀ (U : complexWhittakerModel r ds (-a)) (Φ : 𝓢(Rect, ℂ)),
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ n => translateTest k.val Φ)) →
      let W (z : ℂ) (g : G) := continuedValue ν μ d a (operatorToEntry Φ) U.val g z
      (∀ g, Differentiable ℂ (fun z => W z g)) ∧ ∀ z, HasLeftCharacter (-a) (W z)

set_option maxHeartbeats 1050000 in
theorem complexGodementUnlinkedFamily : ComplexGodementUnlinkedFamilyStatement (r := r) := by
  intro ν hν hνr μ a d ds hd hUnl U Φ hΦ W
  let c (p : Fin m → ℂ) : H → ℂ := U.val
  have hUc : Continuous U.val := (contMDiff_of_mem_complexWhittakerModel U.2).continuous
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound U {1} isCompact_singleton
  have hU (S : Set (Fin m → ℂ)) : HasUniformSimpleRootBound S c := by
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hCb⟩ := hN J
    exact ⟨C, hC, fun _ _ g => by simpa only [c, mul_one] using hCb 1 (mem_singleton _) g⟩
  let line (z : ℂ) : Fin n → ℂ := Fin.cons z (0 : Fin m → ℂ)
  have hline : Differentiable ℂ line := by
    apply differentiable_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact differentiable_id
    · exact differentiable_const _
  have hW (g : G) : Differentiable ℂ (fun z => W z g) := by
    have h := differentiable_generatorValue ν μ a d (operatorToEntry Φ) c (fun _ => hUc)
      (fun g₀ => differentiable_const (U.val g₀)) (fun p => ⟨1, one_pos, hU _⟩) g
    exact h.comp hline
  refine ⟨hW, fun z u g => ?_⟩
  classical
  let I : Finset ℝ := (ds.map fun c => c.exponent.im).toFinset
  obtain ⟨b, hb⟩ := I.finite_toSet.bddAbove
  let z₀ : ℂ := ((b + 1 - d.exponent.im : ℝ) : ℂ) * Complex.I
  have h₀ : b < (d.exponent + z₀).im := by
    simp only [z₀, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero]
    linarith
  have hNear : ∀ᶠ w : ℂ in 𝓝 z₀, b < (d.exponent + w).im :=
    (isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_const.add continuous_id))).mem_nhds h₀
  obtain ⟨l, p, hp⟩ := exists_characterList ds hd
  have he (w : ℂ) (hw : b < (d.exponent + w).im) : HasLeftCharacter (-a) (W w) := by
    let l' : Fin n → ℤ := Fin.cons d.weight l
    let p' : Fin n → ℂ := Fin.cons (d.exponent + w) p
    have hRet : retainedCharacters l' p' = ds := by
      change characterList (Fin.tail l') (Fin.tail p') = ds
      rw [show Fin.tail l' = l from Fin.tail_cons _ _, show Fin.tail p' = p from Fin.tail_cons _ _, hp]
    have hAdded : addedCharacter l' p' = shiftedCharacter d w := rfl
    have hChar : characterList l' p' = shiftedCharacter d w :: ds := by
      rw [characterList_cons, hRet, hAdded]
    have hUnl' : IsComplexUnlinked (characterList l' p') := by
      rw [hChar, IsComplexUnlinked, List.pairwise_cons]
      refine ⟨fun c hc => not_linked_of_im_ne ?_, hUnl⟩
      have hmem : c.exponent.im ∈ (I : Set ℝ) := by
        change c.exponent.im ∈ I
        dsimp only [I]
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨c, hc, rfl⟩
      rw [shiftedCharacter_exponent]
      exact ((hb hmem).trans_lt hw).ne'
    have hirr := (complexStandardIrreducibilityUnlinked n (characterList l' p') List.length_ofFn).mpr hUnl'
    let U' : complexWhittakerModel r (retainedCharacters l' p') (-a) := ⟨U.val, hRet.symm ▸ U.2⟩
    have hModel := complexGodementContinuedModel ν μ a l' p' hirr Φ hΦ U'
    have hM : W w ∈ complexWhittakerModel (r + 1) (characterList l' p') (-a) := by
      have hEq : W w = fun g => continuedValue ν μ (addedCharacter l' p') a (operatorToEntry Φ) U'.val g 0 := by
        funext g
        simpa only [hAdded, shiftedCharacter, U', W] using continuedValue_eq_shiftedCharacter ν μ d a (operatorToEntry Φ) U.val g w
      rw [hEq]
      exact hModel
    exact fun v x => complexWhittakerModel_left_equivariant hM v.val v.2 x
  have hEq := AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => (hW (u.val * g)).analyticAt s)
    (fun s _ => ((hW g).const_mul (complexWhittakerCharacter (-a) u.val)).analyticAt s)
    (z₀ := z₀) (hNear.mono fun w hw => he w hw u g)
  exact congrFun hEq z

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
