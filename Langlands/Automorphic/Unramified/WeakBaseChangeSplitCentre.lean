import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.Unramified.WeakBaseChangeCentralCharacter
import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Global.IdeleNormAbsoluteValue

/-! # Compatible twists to the split centre for arithmetic weak base change -/

noncomputable section

universe u uV uW

set_option autoImplicit false

open scoped NNReal NumberField

namespace Langlands.Automorphic

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open CuspidalPairPoles

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)] {r : ℕ}
  {S : CuspidalOperatorRealization F r} {T : CuspidalOperatorRealization E r}

namespace CuspidalSpectralPresentation

/-- Twisting genuine spectral presentations by a character and its norm pullback
preserves the arithmetic weak base change comparison. -/
theorem isArithmeticWeakBaseChangeOf_heckeDeterminantTwist
    (P : CuspidalSpectralPresentation.{u, uV} S) (Q : CuspidalSpectralPresentation.{u, uW} T)
    (χ : HeckeCharacter F) (hbase : Q.spectralSystem.IsArithmeticWeakBaseChangeOf P.spectralSystem) :
    (Q.heckeDeterminantTwist (χ.normComp (L := E))).spectralSystem.IsArithmeticWeakBaseChangeOf
      (P.heckeDeterminantTwist χ).spectralSystem := by
  let χE := χ.normComp (L := E)
  obtain ⟨A, hA⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F χ
  filter_upwards [hbase, A.eventually_cofinite_notMem,
    (P.heckeDeterminantTwist χ).exceptional.eventually_cofinite_notMem,
    SpectralSystem.eventually_avoidsAbove (F := F) (Q.heckeDeterminantTwist χE).exceptional]
    with v hv hvA hPχ hQχ
  obtain ⟨hP, hQ, he, hpower⟩ := hv
  refine ⟨hPχ, hQχ, he, fun w => ?_⟩
  change Eigenvalues.scale (χE.finiteUniformizerValue w.1)
      (Q.spectralSystem.eigenvalues w.1 (hQ w)) =
    (Eigenvalues.scale (χ.finiteUniformizerValue v) (P.spectralSystem.eigenvalues v hP)).power _
  rw [Eigenvalues.power_scale, hpower w,
    HeckeCharacter.normComp_finiteUniformizerValue χ v w (he w) (hA v hvA)]

end CuspidalSpectralPresentation

namespace CuspidalOperatorRealization

/-- The compatible twists preserve weak base change on the underlying cuspidal classes. -/
theorem heckeDeterminantTwist_isWeakBaseChangeOf
    (χ : HeckeCharacter F)
    (hbase : IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW} T.isoClass S.isoClass) :
    IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW}
      (T.heckeDeterminantTwist (χ.normComp (L := E))).isoClass
      (S.heckeDeterminantTwist χ).isoClass := by
  obtain ⟨P, Q, hPQ⟩ := (IsoClass.isWeakBaseChangeOf_isoClass_iff.{u, u, uV, uW} T S).mp hbase
  exact (IsoClass.isWeakBaseChangeOf_isoClass_iff _ _).mpr
    ⟨P.heckeDeterminantTwist χ, Q.heckeDeterminantTwist (χ.normComp (L := E)),
      P.isArithmeticWeakBaseChangeOf_heckeDeterminantTwist Q χ hPQ⟩

private theorem centralIdeleCharacter_positiveRealIdeles_of_splitCentre
    {ω : HeckeCharacter F} (hω : S.HasCentralCharacter ω) (hS : IsTrivialOnSplitCentre S)
    (a : ℝ≥0ˣ) : centralIdeleCharacter F ω (PositiveRealIdeles.full F a) = 1 := by
  obtain ⟨f, x, hfx⟩ := S.realization.exists_evaluate_ne_zero S.irreducible
  have h := S.realization.centralCharacter_evaluate ω hω f (PositiveRealIdeles.full F a) x
  rw [hS _ (isPositiveArchimedeanScalar_positiveRealIdeles a) f x] at h
  exact Units.ext (mul_right_cancel₀ hfx (h.symm.trans (one_mul _).symm))

omit [CompactSpace (AdeleQuotient E)] in
private theorem exists_positiveRealIdeles_full {a : IdeleGroup (𝓞 E) E}
    (ha : IsPositiveArchimedeanScalar a) : ∃ t : ℝ≥0ˣ, a = PositiveRealIdeles.full E t := by
  obtain ⟨hfin, t, ht, hinf⟩ := ha
  let tUnit : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (by
    intro h
    exact ht.ne' (congrArg NNReal.toReal h))
  refine ⟨tUnit, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext v
    apply (InfinitePlace.Completion.extensionEmbedding v).injective
    rw [hinf v]
    exact (PositiveRealIdeles.extensionEmbedding_full E v tUnit).symm
  · exact hfin

set_option maxHeartbeats 2000000 in
/-- Split-centre triviality passes from a cuspidal realization to an arithmetic weak
base change because the upper central character is the norm pullback. -/
theorem isTrivialOnSplitCentre_of_isWeakBaseChangeOf
    (hbase : IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW} T.isoClass S.isoClass)
    (hS : IsTrivialOnSplitCentre S) : IsTrivialOnSplitCentre T := by
  obtain ⟨ω, hω, -⟩ := S.realization.existsUnique_hasCentralCharacter S.irreducible
  have hωE := hasCentralCharacter_normComp_of_isWeakBaseChangeOf hω hbase
  intro a ha f x
  obtain ⟨t, rfl⟩ := exists_positiveRealIdeles_full ha
  have hnorm : centralIdeleCharacter E (HeckeCharacter.normComp (L := E) ω)
      (PositiveRealIdeles.full E t) =
      centralIdeleCharacter F ω (PositiveRealIdeles.full F (t ^ Module.finrank F E)) := by
    change ω (ideleClassNorm (K := F) (QuotientGroup.mk (PositiveRealIdeles.full E t))) = _
    rw [ideleClassNorm_mk, ideleNorm_positiveRealIdeles]
    rfl
  have h := T.realization.centralCharacter_evaluate _ hωE f (PositiveRealIdeles.full E t) x
  rw [hnorm, centralIdeleCharacter_positiveRealIdeles_of_splitCentre hω hS,
    Units.val_one, one_mul] at h
  exact h

/-- A determinant norm power and its norm pullback put both realizations on the split-centre
quotients, retaining their weak base change relation. -/
def WeakBaseChangeSplitCentreStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r),
    IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW} T.isoClass S.isoClass →
    ∃ s : ℂ,
      let χ := HeckeCharacter.normPower F s
      let Sχ := S.heckeDeterminantTwist χ
      let Tχ := T.heckeDeterminantTwist (χ.normComp (L := E))
      IsTrivialOnSplitCentre Sχ ∧ IsTrivialOnSplitCentre Tχ ∧
        IsoClass.IsWeakBaseChangeOf.{u, u, uV, uW} Tχ.isoClass Sχ.isoClass

/-- Normalize the lower realization by a norm power and transport its split-centre
triviality to the compatible upper twist. -/
theorem weakBaseChangeSplitCentre : WeakBaseChangeSplitCentreStatement.{u, uV, uW} := by
  intro F E _ _ _ _ _ _ _ r S T hbase
  obtain ⟨l, hS⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre S
  have hbaseχ := heckeDeterminantTwist_isWeakBaseChangeOf (HeckeCharacter.normPower F (-l)) hbase
  exact ⟨-l, hS, isTrivialOnSplitCentre_of_isWeakBaseChangeOf hbaseχ hS, hbaseχ⟩

end CuspidalOperatorRealization

end Langlands.Automorphic
