import Langlands.Global.Factors.CuspidalPairSquareIntegrableTwistStatement
import Langlands.Global.Factors.CuspidalPairSchemeAutomorphy
import Langlands.Global.Factors.CuspidalPairTwistedSections
import Langlands.Global.Factors.CuspidalPairBlockModulus
import Langlands.Global.Factors.CuspidalPairInducedIntegrability
import Langlands.Global.Factors.CuspidalPartialPairOrderOneReduction
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof

/-! # Square-integrable imaginary twists of cuspidal-pair sections -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints AdelicBlockEisensteinGeometry
open AdelicBlockParabolic AdelicBlockDeterminantCharacter AdelicBlockScalarSections
open PrimitiveAdelicHeight CuspidalPairPoles
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

section Normalizers

variable {F : Type} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

private theorem dual_hasUnitaryCentralCharacter (T : CuspidalOperatorRealization F r)
    (hT : HasUnitaryCentralCharacter T) : HasUnitaryCentralCharacter (dualRealization T) := by
  obtain ⟨ω, hωu, hω⟩ := HasUnitaryCentralCharacter.conjugate hT
  have hd : (dualRealization T).realization.IsContragredientOf T.realization :=
    (cuspidalContragredientExistence F r T).choose_spec
  obtain ⟨e⟩ := (RankinSelbergGlobal.SelfPair.conjugate_isContragredientOf T hT).nonempty_equivalence hd
  exact ⟨ω, hωu, e.hasCentralCharacter hω⟩

private theorem exists_imaginaryNormalizer (T : CuspidalOperatorRealization F r)
    (hT : HasUnitaryCentralCharacter T) :
    ∃ a : ℝ, IsTrivialOnSplitCentre (T.heckeDeterminantTwist
      (HeckeCharacter.normPower F (-((a : ℂ) * Complex.I)))) := by
  obtain ⟨s, hs⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T
  obtain ⟨ω, hu, hω⟩ := hT
  have hsr := CuspidalPartialPairOrderOne.normalizer_re_eq_zero hω hu hs
  have he : s = (s.im : ℂ) * Complex.I := Complex.ext (by simp [hsr]) (by simp)
  exact ⟨s.im, he ▸ hs⟩

end Normalizers

variable (F : Type) [Field F] [NumberField F] (r t : ℕ)

local notation "N" => (r + t + 2)
local notation "B" => blockShape r t
local notation "𝕜" => CommRingCat.of F
local notation "G" => groupScheme (Fin N) 𝕜
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin N) 𝕜 wt
local notation "M" => blockLeviScheme (Fin N) 𝕜 wt
local notation "p" => blockParabolicHom (Fin N) 𝕜 wt
local notation "l" => blockLeviInclusion F B
local notation "iU" => blockUnipotentInclusion F B
local notation "K" => standardCompactPoints F N
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "e" => adelicHomeomorph F N
local notation "A" => CommAlgCat.of F (Adeles F)

local instance squareIntegrableTwistGLAffine : IsAffine (G).X.left := isAffine_groupScheme (Fin N) _
local instance squareIntegrableTwistGLFiniteType : LocallyOfFiniteType (G).X.hom :=
  have := (isConnectedReductive_generalLinear F (Fin N)).smooth
  inferInstance
local instance squareIntegrableTwistParabolicAffine : IsAffine (P).X.left := blockParabolic_isAffine F B
local instance squareIntegrableTwistParabolicFiniteType : LocallyOfFiniteType (P).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType (isClosedSubgroup_blockParabolicHom (Fin N) 𝕜 wt)
local instance squareIntegrableTwistLeviAffine : IsAffine (M).X.left :=
  have := (blockLevi_isConnectedReductive F B).isAffineHom
  isAffine_of_isAffineHom (M).X.hom
local instance squareIntegrableTwistLeviFiniteType : LocallyOfFiniteType (M).X.hom :=
  have := (blockLevi_isConnectedReductive F B).smooth
  inferInstance

omit [NumberField F] in
private theorem determinantParameter_neg_imaginary (a : Fin ((B).length) → ℝ) :
    determinantParameter F B (fun i => -((a i : ℂ) * Complex.I)) =
      -imaginaryParameter F P (∑ i, a i ⊗ₜ[ℤ] parabolicBlockCharacter B 𝕜 i) := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  unfold determinantParameter
  apply Finset.sum_congr rfl
  intro i _
  simp only [imaginaryParameter, AlgebraTensorModule.map_tmul, LinearMap.toSpanSingleton_apply,
    LinearMap.id_coe, id_eq, Complex.real_smul, TensorProduct.neg_tmul]

variable {F r t}

private theorem splitEquivariant_of_fixedBlockScalars
    (S : ∀ i : Fin ((B).length), OperatorRealization F ((B).size i))
    (hS : ∀ i (z : ℝ≥0ˣ) (v : (S i).Space) x,
      ContinuousRationalFunctions.evaluate F ((B).size i) ((S i).toContinuous v)
        (AdelicGL.scalar F ((B).size i) (PositiveRealIdeles.full F z) * x) =
        ContinuousRationalFunctions.evaluate F ((B).size i) ((S i).toContinuous v) x)
    (f : RealizedSections F B S) : IsSplitComponentEquivariant p l (f.val ∘ e) := by
  intro a ha g
  choose z hz using fun i => exists_matrixLeviPoint_eq_positiveScalar F B ha i
  let m := matrixLeviPoint F B a
  have hfixed (w : FullLevi F B → ℂ) (hw : w ∈ coefficientValues F B S) (b : FullLevi F B) :
      w (m * b) = w b := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      unfold blockCoefficient
      refine Finset.prod_congr rfl fun i _ => ?_
      change ContinuousRationalFunctions.evaluate F ((B).size i) ((S i).toContinuous (v i))
        (matrixLeviPoint F B a i * b i) = _
      rw [hz i, hS]
    | zero => rfl
    | add w w' _ _ hw hw' => simp only [Pi.add_apply, hw, hw']
    | smul c w _ hw => simp only [Pi.smul_apply, hw]
  obtain ⟨q, k, hk, rfl⟩ := (hK).exists_eq g
  let r₀ := blockParabolicPointsEquiv F B A (map F M P l a)
  let q₀ := blockParabolicPointsEquiv F B A q
  let k₀ : standardCompact F N := ⟨e k, hk⟩
  have hr₀ : r₀ = (B).leviInParabolic (Adeles F) m :=
    blockParabolicPointsEquiv_blockLeviInclusion F B A a
  have hkq : e (map F P G p q * k) = q₀.val * k₀.val := by
    rw [map_mul]
    rfl
  have hkrq : e (map F P G p (map F M P l a) * (map F P G p q * k)) =
      (r₀ * q₀).val * k₀.val := by
    rw [map_mul, hkq, Subgroup.coe_mul, mul_assoc]
    rfl
  change f.val (e _) = _ * f.val (e _)
  rw [hkrq, hkq, scalarSection_apply_mul F B _ f (r₀ * q₀) k₀,
    scalarSection_apply_mul F B _ f q₀ k₀,
    parameterPower_halfModulus_of_blockScalar F r t a (fun i => PositiveRealIdeles.full F (z i)) hz,
    map_mul, Units.val_mul, map_mul, hr₀, parabolicHalfCharacter_section, (B).leviProjection_section,
    hfixed _ (f.property.2 k₀), mul_assoc]

variable (F r t) in
private theorem squareIntegrableTwist_fieldwise [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (hT : HasUnitaryCentralCharacter T) (hT' : HasUnitaryCentralCharacter T')
    (φ : AdelicGL F N → ℂ) (hφ : IsSection T T' φ) :
    ∃ (y : RealCharacterParameter F P) (ψ : AdelicGroupPoints F G → ℂ),
      (∀ x, φ (e x) = ψ x * (hK).heightPower (imaginaryParameter F P y) x) ∧
      ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d (G).X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth),
        IsSquareIntegrableInducedForm K (hK).isCompact (MatrixRepresentation.standard (Fin N) 𝕜)
          hsmooth hcalc p iU l ψ := by
  obtain ⟨a₀, ha₀⟩ := exists_imaginaryNormalizer T hT
  obtain ⟨a₁, ha₁⟩ := exists_imaginaryNormalizer (dualRealization T') (dual_hasUnitaryCentralCharacter T' hT')
  let a : Fin ((B).length) → ℝ := Fin.cases a₀ (fun _ => a₁)
  let y : RealCharacterParameter F P := ∑ i, a i ⊗ₜ[ℤ] parabolicBlockCharacter B 𝕜 i
  let s (i : Fin ((B).length)) : ℂ := -((a i : ℂ) * Complex.I)
  let lam := determinantParameter F B s
  let ψ := (hK).parameterTwist (φ ∘ e) lam
  have hparam : lam = -imaginaryParameter F P y := determinantParameter_neg_imaginary F r t a
  refine ⟨y, ψ, fun x => ?_, ?_⟩
  · change φ (e x) = (φ (e x) * (hK).heightPower lam x) * (hK).heightPower (imaginaryParameter F P y) x
    rw [hparam, IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, mul_assoc, ← Complex.exp_add,
      map_neg, LinearMap.neg_apply, neg_add_cancel, Complex.exp_zero, mul_one]
  intro d hsmooth hcalc
  let S := blockRealizations T T'
  let R := determinantTwistedRealizations F B S s
  obtain ⟨g, hg⟩ := exists_smoothSection_parameterTwist F B S s (smoothSection hφ) hsmooth
  rw [smoothSectionOnScheme_smoothSection hφ] at hg
  change smoothSectionOnScheme F B R g = ψ at hg
  have hrealized : ψ = (fun x => g.val.val.val (e x)) := hg.symm
  let T₀ := T.heckeDeterminantTwist (HeckeCharacter.normPower F (-((a₀ : ℂ) * Complex.I)))
  let T₁ := (dualRealization T').heckeDeterminantTwist (HeckeCharacter.normPower F (-((a₁ : ℂ) * Complex.I)))
  have hRcuspidal : ∀ i, (R i).IsCuspidal := by
    have h : ∀ i : Fin 2, (R i).IsCuspidal := by
      intro i
      fin_cases i
      · exact T₀.cuspidal
      · exact T₁.cuspidal
    exact h
  have hRadm : ∀ i, (R i).IsJointlyAdmissible := by
    have h : ∀ i : Fin 2, (R i).IsJointlyAdmissible := by
      intro i
      fin_cases i
      · exact T₀.isJointlyAdmissible
      · exact T₁.isJointlyAdmissible
    exact h
  have hauto : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      ((K).comap (ofInfinite F G).toMonoidHom) (MatrixRepresentation.standard (Fin N) 𝕜) ψ := by
    rw [standardCompactPoints_comap_ofInfinite, ← hg]
    exact SchemeSection.isAutomorphicFunctionOn F B R (by omega) hRadm hsmooth hcalc g
  have heq : IsSplitComponentEquivariant p l ψ := by
    rw [hrealized]
    apply splitEquivariant_of_fixedBlockScalars R _ g.val.val
    have h (i : Fin 2) (z : ℝ≥0ˣ) (v : (R i).Space) (x : AdelicGL F ((B).size i)) :
        ContinuousRationalFunctions.evaluate F ((B).size i) ((R i).toContinuous v)
          (AdelicGL.scalar F ((B).size i) (PositiveRealIdeles.full F z) * x) =
          ContinuousRationalFunctions.evaluate F ((B).size i) ((R i).toContinuous v) x := by
      fin_cases i
      · exact ha₀ _ (isPositiveArchimedeanScalar_positiveRealIdeles z) v x
      · exact ha₁ _ (isPositiveArchimedeanScalar_positiveRealIdeles z) v x
    exact h
  exact ⟨hauto, heq, integrable_weightedSquare_of_cuspidal F B R hRcuspidal g ψ hrealized
    hauto.1 heq hauto.2.1.1⟩

/-- Each cuspidal-pair section has a square-integrable normalization by an imaginary block
parameter. -/
theorem cuspidalPairSquareIntegrableTwist : CuspidalPairSquareIntegrableTwistStatement :=
  fun F _ _ _ r t => squareIntegrableTwist_fieldwise F r t

end Langlands.Global.CuspidalPairEisenstein
