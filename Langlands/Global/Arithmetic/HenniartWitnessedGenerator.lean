import Langlands.VirtualRepresentation.Global.UnitaryInductionGenerator
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentation
import Langlands.Automorphic.CuspidalSpectralUniverseLift
import Langlands.Automorphic.AssociatedUnitaryCentralCharacter
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.DeterminantMultipleSpectrum
import Langlands.Automorphic.Unramified.IsobaricWeilAssociation
import Langlands.Automorphic.WeakInductionAssociationReduction
import Langlands.Automorphic.CuspidalDeterminantMultipleProof
import Langlands.Automorphic.HeckeDeterminantTwistAssociationProof
import Langlands.Global.Factors.RelativeTwistWitnessedGenerator
import Langlands.Global.HeckeNormTwist
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.VirtualRepresentation.Weil.ExactOperations

/-!
# Witnessed generators from weakly associated unitary representations

An irreducible unitary representation `S` of `W_{E/F}` weakly associated with a cuspidal
class gives a witnessed relative generator at every finite place `v`, whose Weil element
expands the restriction of `S` along a given local map at `v`.
-/

noncomputable section

set_option autoImplicit false

universe uW uP uV uQ

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Automorphic
open scoped WithZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  {c : FundamentalClass.ClassFamily.{0}}

/-- Weak association with the class of `T` holds for the spectral system of every
presentation of `T`. -/
theorem isWeaklyAssociated_of_isWeaklyAssociatedClass
    (S : FiniteRepresentation.{0, 0, uV} ℂ (RelativeWeilGroup c F E)) {r : ℕ}
    (T : CuspidalOperatorRealization F r)
    (hS : RelativeWeilGroup.IsWeaklyAssociatedClass.{0, uV, uP} S T.isoClass)
    (Q : CuspidalSpectralPresentation.{0, uQ} T) :
    RelativeWeilGroup.IsWeaklyAssociated S Q.spectralSystem := by
  obtain ⟨P, hP⟩ := (RelativeWeilGroup.isWeaklyAssociatedClass_isoClass_iff S T).mp hS
  have h1 := CuspidalOperatorRealization.sameEulerPolynomials_scale_of_isDeterminantMultiple T T P Q
    (OperatorRealization.isDeterminantMultiple_refl T.realization)
  have h2 : Unramified.SpectralSystem.scale (1 : HeckeCharacter F).finiteUniformizerValue
      P.spectralSystem = P.spectralSystem :=
    Unramified.SpectralSystem.scale_one P.spectralSystem
  rw [h2] at h1
  exact hP.of_sameEulerPolynomials h1

/-- An irreducible unitary representation `S` of `W_{E/F}`, weakly associated with a
cuspidal class, gives a witnessed generator at `v` whose Weil element expands the
restriction of `S` along the local map `ι`. The inputs are the existence of presentations
irreducible at every finite place, the central-character comparison and Henniart's
Théorème 2.4. -/
theorem exists_witnessedGenerator_realizeExact
    (hcalip : CuspidalAllLocalIrreduciblePresentationExistenceStatement.{0, uP})
    (hacc : RelativeWeilGroup.AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP})
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c) (v : FinitePlace F)
    (S : FiniteRepresentation.{0, 0, uW} ℂ (RelativeWeilGroup c F E))
    (hirr : S.IsIrreducible) (hu : S.IsUnitary) {r : ℕ}
    (π : CuspidalOperatorRealization.IsoClass F r)
    (hπ : RelativeWeilGroup.IsWeaklyAssociatedClass.{0, uW, uP} S π)
    (w : FinitePlacesAbove E v)
    (rec : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 rec ι) :
    ∃ (hS : S.IsContinuous) (d : WitnessedGenerator.{0, uW, uP} F E c v),
      LocalWeil.realizeExact (padicField v)
          (LocalWeil.includeUnitary (padicField v) d.weilElement) =
        localExactClass F E c v S hS ι := by
  obtain ⟨T, rfl⟩ := π.exists_representative
  obtain ⟨P₀, -⟩ := (RelativeWeilGroup.isWeaklyAssociatedClass_isoClass_iff S T).mp hπ
  obtain ⟨Q, hQ⟩ := hcalip F r T P₀
  have hassoc := isWeaklyAssociated_of_isWeaklyAssociatedClass S T hπ Q.universeLift.{uP}
  have hlirr :=
    (CuspidalSpectralPresentation.universeLift_localComponent_isIrreducible_iff.{uP} Q v).mpr
      (hQ v).1
  have hladm :=
    (CuspidalSpectralPresentation.universeLift_localComponent_isAdmissible_iff.{uP} Q v).mpr
      (hQ v).2
  have hcent := RelativeWeilGroup.hasUnitaryCentralCharacter_of_associatedCentralCharacter
    F E c hacc hc S T hπ hu
  obtain ⟨B, σ, hσ, ⟨e⟩⟩ := hasi c hc F E S T hirr hu hcent hπ _ v hlirr hladm
  exact ⟨hassoc.1, WitnessedGenerator.ofUnitaryInduction F E c v S hirr hu T _ hassoc w rec ι
    hι hlirr hladm B σ hσ e, localUnitaryExpansion_spec F E c v S hassoc.1 hu ι⟩

omit [CompactSpace (AdeleQuotient F)] in
/-- An imaginary power of the idelic norm takes any prescribed modulus-one value at the
canonical uniformizer of `F_v`. -/
theorem exists_unitaryNormPower_uniformizerUnit (v : FinitePlace F) (z : ℂˣ)
    (hz : ‖(z : ℂ)‖ = 1) :
    ∃ t : ℝ, (HeckeCharacter.unitaryNormPower F t).finiteComponent v
      (padicField v).canonicalTopologicalData.uniformizerUnit = z := by
  let b : (FiniteCompletion F v)ˣ := (padicField v).canonicalTopologicalData.uniformizerUnit
  have hb : Valued.v (b : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    CompletionPadic.valued_uniformizerUnit_padicFieldAt v rfl
  have hlt : ‖(b : v.adicCompletion F)‖ < 1 := by
    apply (Valued.toNormedField.norm_lt_one_iff (Γ₀ := ℤᵐ⁰)).mpr
    rw [hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hpos : 0 < ‖(b : v.adicCompletion F)‖ := norm_pos_iff.mpr b.ne_zero
  have hlog : Real.log ‖(b : v.adicCompletion F)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  refine ⟨Complex.arg z / Real.log ‖(b : v.adicCompletion F)‖, Units.ext ?_⟩
  rw [HeckeCharacter.unitaryNormPower_finiteComponent]
  change Complex.exp (((Complex.arg z / Real.log ‖(b : v.adicCompletion F)‖ *
    Real.log ‖(b : v.adicCompletion F)‖) : ℝ) * Complex.I) = (z : ℂ)
  rw [div_mul_cancel₀ _ hlog]
  simpa only [hz, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I (z : ℂ)

/-- Twisting by an unramified modulus-one character of `W_{F_v}` preserves the Weil
elements of witnessed generators, given the local transfer reciprocity input. -/
theorem exists_witnessedGenerator_unramifiedTwist
    (htransfer : RelativeWeilGroup.LocalTransferReciprocityStatement.{0})
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c) {v : FinitePlace F}
    (d : WitnessedGenerator.{0, uW, uP} F E c v) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ d' : WitnessedGenerator.{0, uW, uP} F E c v,
      LocalWeil.realizeExact (padicField v)
          (LocalWeil.includeUnitary (padicField v) d'.weilElement) =
        ExactGrothendieckGroup.continuousTwist
          (Weil.Local.localUnramifiedCharacter (padicField v) z)
          (LocalWeil.realizeExact (padicField v)
            (LocalWeil.includeUnitary (padicField v) d.weilElement)) := by
  obtain ⟨t, ht⟩ := exists_unitaryNormPower_uniformizerUnit v z hz
  obtain ⟨e, he, -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness _
    (padicField v) (padicField v).canonicalTopologicalData
  let Ω := HeckeCharacter.unitaryNormPower F t
  let μ := quasicharacterBase v (Ω.finiteComponent v)
  have hμu := CompletionPadic.isUnramifiedCharacter_quasicharacterAt v rfl Ω
      (HeckeCharacter.unitaryNormPower_isUnramifiedAt F t v)
  have hμ : ∀ a, ‖(μ a : ℂ)‖ = 1 := fun a =>
    HeckeCharacter.unitaryNormPower_isUnitary F t _
  obtain ⟨d', hd', -⟩ := d.exists_heckeTwist hc cuspidalDeterminantMultiple
    RelativeWeilGroup.presentedDeterminantMultipleAssociation htransfer Ω
    (HeckeCharacter.unitaryNormPower_isUnitary F t) e he μ hμ (fun a => rfl)
  refine ⟨d', ?_⟩
  have hw : LocalFactor.RankOne.weilCharacter (padicField v) e μ =
      Weil.Local.localUnramifiedCharacter (padicField v) z := by
    apply ContinuousMonoidHom.toMonoidHom_injective
    change Correspondence.weilCharacter (padicField v) e μ = _
    rw [Correspondence.weilCharacter_eq_localUnramifiedCharacter (padicField v) he (χ := μ) hμu]
    congr 2
  rw [hd']
  change Weil.realizeExact _ (Weil.includeUnitary _ (Weil.unitaryTwistLatticeEquiv
    (LocalFactor.RankOne.weilCharacter (padicField v) e μ) _ d.weilElement)) = _
  have := Weil.ExactExpansion.unitaryTwist (G := Weil.Local.localWeilGroup (padicField v))
    (x := LocalWeil.realizeExact (padicField v)
      (LocalWeil.includeUnitary (padicField v) d.weilElement)) rfl
    (LocalFactor.RankOne.weilCharacter (padicField v) e μ)
    (LocalWeil.norm_weilCharacter_eq_one (padicField v) e μ hμ)
  rw [← hw]
  exact this

end Langlands.VirtualRepresentation.RelativeGlobal
