import Langlands.Correspondence.AssemblyLSegmentReduction
import Langlands.Weil.Local.AssemblyProof
import Langlands.LocalField.Normalization.Proof

/-!
# Twisted pair L compatibility of supercuspidal correspondences

Every supercuspidal correspondence satisfies
`TwistedSupercuspidalPairLCompatibility`: twist compatibility with the
quasi-character `|·|^x` identifies `ν^x c0 σ` with `c0 (ω^x σ)`, and pair L
compatibility at `(ω^x σ, τ)` gives the L identity.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open Polynomial PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyLTwistFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyLTwistGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Under a geometrically normalized reciprocity candidate, the norm character of
the Weil group is the normalized absolute value of the reciprocity image. -/
theorem localNormCharacter_eq_normalizedAbs {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (w : Weil.Local.localWeilGroup F) :
    (Weil.Local.localNormCharacter F w : ℂ) =
      ((F.canonicalTopologicalData.normalizedAbs
        (LocalFactor.RankOne.reciprocityUnits F e w : F.Carrier) : ℝ) : ℂ) := by
  have hord : F.canonicalTopologicalData.ord
      (LocalFactor.RankOne.reciprocityUnits F e w : F.Carrier) =
        Weil.Local.localDegreeInt F w :=
    congrArg (fun f => Multiplicative.toAdd
      (f (LocalClassField.WeilQuotients.projection (Weil.Local.localResidueDegree F) w))) he.1
  rw [Weil.Local.localNormCharacter_apply,
    F.canonicalTopologicalData.normalizedAbs_of_ne_zero (Units.ne_zero _), hord]
  push_cast
  rfl

/-- The reciprocity map of a candidate, from the Weil group onto `F^×`, is
surjective. -/
theorem reciprocityUnits_surjective (e : ReciprocityCandidate F) :
    Function.Surjective (LocalFactor.RankOne.reciprocityUnits F e) := by
  intro a
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e.symm a)
  refine ⟨w, ?_⟩
  change e (QuotientGroup.mk w) = a
  rw [hw]
  exact e.apply_symm_apply a

/-- The field quasi-character `|·|^x`, obtained by transporting `ω^x` along the
reciprocity candidate `e`. -/
def normPowerQuasiCharacter (e : ReciprocityCandidate F) (x : ℕ) : QuasiCharacter F :=
  LocalFactor.RankOne.fieldCharacter F e (Weil.Local.localNormCharacter F ^ x)

theorem weilCharacter_normPowerQuasiCharacter (e : ReciprocityCandidate F) (x : ℕ) :
    LocalFactor.RankOne.weilCharacter F e (normPowerQuasiCharacter F e x) =
      Weil.Local.localNormCharacter F ^ x :=
  LocalFactor.RankOne.weilCharacter_fieldCharacter F e _

/-- Under geometric normalization, `normPowerQuasiCharacter F e x` is `|·|^x`. -/
theorem normPowerQuasiCharacter_apply {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (x : ℕ) (a : F.Carrierˣ) :
    (normPowerQuasiCharacter F e x a : ℂ) =
      ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^ x := by
  obtain ⟨w, rfl⟩ := reciprocityUnits_surjective F e a
  have h := DFunLike.congr_fun (weilCharacter_normPowerQuasiCharacter F e x) w
  rw [LocalFactor.RankOne.weilCharacter_apply] at h
  rw [h, ← localNormCharacter_eq_normalizedAbs F he w]
  simp

/-- Under geometric normalization, `|·|^x ∘ det` is the determinant power
character `|det|^x`. -/
theorem determinantQuasiCharacter_normPowerQuasiCharacter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (x : ℕ) (n : ℕ+) :
    determinantQuasiCharacter F n (normPowerQuasiCharacter F e x) =
      F.canonicalTopologicalData.determinantPowerCharacter (n : ℕ) (x : ℝ) := by
  ext g
  rw [coe_realPowerCharacter, determinantNorm_coe, Real.rpow_natCast]
  change (normPowerQuasiCharacter F e x (GeneralLinear.determinant g) : ℂ) = _
  rw [normPowerQuasiCharacter_apply F he]
  push_cast
  rfl

/-- The zero-monodromy pair class of an irreducible Weil class is the class of the
zero-monodromy pair of any representative. -/
theorem weilPairClass_eq_classOf {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n)
    (B : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hB : FiniteRepresentation.classOf B = weilClassForget F σ) :
    weilPairClass F σ = WeilDeligneRepresentation.classOf
      (WeilDeligneRepresentation.zeroMonodromy (Weil.Local.localNormCharacter F).toMonoidHom B) := by
  unfold weilPairClass
  rw [← hB]
  rfl

/-- Every supercuspidal correspondence is compatible with pair L-factors after
twisting the first factor by `ν^x`, `x ∈ ℕ`. -/
theorem IsSupercuspidalCorrespondence.twistedSupercuspidalPairLCompatibility
    {c0 : SupercuspidalMap.{uF, uP, uA} F} (hc0 : IsSupercuspidalCorrespondence F c0) :
    TwistedSupercuspidalPairLCompatibility F c0 := by
  obtain ⟨_, _, e, he, _, _, htw, eC, ε, hε, _, hpair⟩ := hc0
  intro ψ ν hνψ d t σ τ B B' hσ hτ A A' hA hA' x
  set χ := normPowerQuasiCharacter F e x with hχdef
  have hdet := determinantQuasiCharacter_normPowerQuasiCharacter F he x d.succPNat
  have hopen : IsOpen ((determinantQuasiCharacter F d.succPNat χ).ker :
      Set (GeneralLinear (d.succPNat : ℕ) F.Carrier)) := by
    rw [hdet]
    exact F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter _ _
  set σ' := FiniteRepresentation.continuousIrreducibleTwistEquiv
    (LocalFactor.RankOne.weilCharacter F e χ) (d.succPNat : ℕ) σ with hσ'def
  have hc : c0 d.succPNat σ' = (GeneralLinear.SupercuspidalRep.twist
      (determinantQuasiCharacter F d.succPNat χ) hopen
      (GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom) A).isoClass := by
    have h := (isSupercuspidalCharacterTwist_iff_eq_twist F χ hopen _ _).mp (htw _ σ χ)
    rw [← hA] at h
    exact h
  obtain ⟨⟨P, hP, hL⟩, _⟩ := (hpair ψ d t σ' τ).2 ν hνψ
  rw [hc, ← hA'] at hP
  change RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν
    (Langlands.twist (determinantQuasiCharacter F d.succPNat χ) A.obj.representation)
    A'.obj.representation P at hP
  rw [hdet] at hP
  refine ⟨P, hP, ?_⟩
  have hpow : (LocalFactor.RankOne.weilCharacter F e χ).toMonoidHom =
      (Weil.Local.localNormCharacter F).toMonoidHom ^ x := by
    rw [hχdef, weilCharacter_normPowerQuasiCharacter]
    refine MonoidHom.ext fun w => ?_
    rw [MonoidHom.pow_apply]
    exact ContinuousMonoidHom.pow_apply _ _ _
  have hσ' : FiniteRepresentation.classOf (FiniteRepresentation.twist
      ((Weil.Local.localNormCharacter F).toMonoidHom ^ x) B) = weilClassForget F σ' := by
    rw [hσ'def, weilClassForget, FiniteRepresentation.forget_continuousIrreducibleTwistEquiv,
      ← weilClassForget, ← hσ, FiniteRepresentation.twistClass_classOf, hpow]
  rw [weilPairClass_eq_classOf F σ' _ hσ', weilPairClass_eq_classOf F τ B' hτ] at hL
  exact hL

/-- Twisted supercuspidal L inheritance holds. -/
theorem supercuspidalTwistedPairLInheritance :
    SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F :=
  fun _ hc0 => hc0.twistedSupercuspidalPairLCompatibility F

/-- Pair L-factor inheritance of the assembly from multisegment datum existence,
JPSS (9.5) in product form, arithmetic multiplicativity, the segment-head L
formula of Henniart 2002, §2.6 and the arithmetic block-pair formula. -/
theorem assemblyLInheritance_of_segmentHeads_of_blockPairs
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F :=
  assemblyLInheritance_of_segmentHeads F hP hJ hD hH hB
    (supercuspidalTwistedPairLInheritance F)

end Langlands.Correspondence
