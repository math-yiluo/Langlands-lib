import Langlands.Algebra.NumberFieldReducedNormLocalityProof
import Langlands.GroupScheme.Rational.TotallyComplexTrialitarianCyclicReduction
import Langlands.GroupScheme.Rational.TotallyComplexCubicSplitA2Cocycles
import Langlands.GroupScheme.Rational.TrialitarianCubicSplitTorusStatement
import Langlands.GroupScheme.Rational.TrialitarianCubicRestriction
import Langlands.GroupScheme.Rational.TrialitarianPureTwistIsotropic

/-! # The totally imaginary cyclic case from a cubic-split maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.CentralSimple

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- The cyclic cubic case of quasi-split trialitarian vanishing reduces to
finding a maximal torus over the base split by the cubic diagram field. -/
theorem totallyComplexQuasiSplitCyclicTrialitarian_of_cubicSplitTorus
    (htorus : TrialitarianCubicSplitMaximalTorusStatement.{u}) :
    TotallyComplexQuasiSplitCyclicTrialitarianCocycleVanishingStatement.{u} := by
  classical
  intro F _ _ _ G _ _ d e hsc ha hG hD hno heven L _ _ _ _ ξ
  obtain ⟨H, E, hAff, hE⟩ := finiteGaloisTwistExistence F L G G inferInstance
    (AutomorphicAction.conjugation (𝟙 G)) ξ
  let : IsAffineHom H.X.hom := hAff
  let eL := E.toBaseChangeIso
  have hscH := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
    ((isSimplyConnectedFieldExtension F L G hsc).of_iso eL.symm)
  let : Smooth H.X.hom := hscH.isSemisimple.isConnectedReductive.smooth
  by_cases han : IsAnisotropic H
  · let K := d.starField
    let : FiniteDimensional F K := d.finiteDimensional_starField
    let : IsGalois F K := d.isGalois_starField
    have hnf : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
        ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a = a := by
      rintro ⟨a, ha, hf⟩
      obtain ⟨σ, hσ⟩ := hno a ha
      exact hσ (hf σ)
    have hdeg : Module.finrank F K = 3 := d.finrank_starField_of_D4_even e hD hnf heven
    have hξK := Cocycle.isTrivial_baseChange_starField_of_quasiSplit d e hD hsc ha hG L ξ
    obtain ⟨eK⟩ := LocalGroupIso.HasDiscrepancy.nonempty_iso_baseChange_of_isTrivial hE hξK
    obtain ⟨S, s, hs, hS⟩ := d.exists_splitMaximalTorus_starField hG
    have hsplit : ∃ (T : CommGroupScheme (Spec (CommRingCat.of K)))
        (j : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj H),
        IsMaximalTorus j ∧ IsSplitTorus T.toGrp := ⟨S, s ≫ eK.hom, hs.comp_iso eK, hS⟩
    have haH : IsAbsolutelyAlmostSimple H := IsAbsolutelyAlmostSimple.of_fieldExtension
      ((ha.baseChange_of_algebraicExtension (K := L)).of_iso eL.symm)
    obtain ⟨dH⟩ := titsIndexExistence F H hscH.isSemisimple
    obtain ⟨eH, hDH, hnoH⟩ := hE.exists_trialitarian_numbering d dH e hD hno
    obtain ⟨T, t, ht, hT⟩ := htorus F K hdeg H dH eH hscH haH han hDH hnoH hsplit
    refine hE.isTrivial_of_prescribedTwistTorus hsc hG hscH.isSemisimple.isConnectedReductive ht ?_
    intro M _ _ _ _ ζ
    exact ζ.isTrivial_map_of_cubicSplitTrialitarianTorus dH eH hDH hscH han hdeg
      t ht hT numberFieldReducedNormLocality
  · exact hE.isTrivial_of_trialitarian_isotropic numberFieldReducedNormLocality hsc hG hscH d e hD hno han

/-- Existence of a cubic-split maximal torus in the anisotropic cyclic case
suffices for quasi-split trialitarian vanishing over totally imaginary number fields. -/
theorem totallyComplexQuasiSplitTrialitarian_of_cubicSplitTorus
    (htorus : TrialitarianCubicSplitMaximalTorusStatement.{u}) :
    TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement.{u} :=
  totallyComplexQuasiSplitTrialitarian_of_cyclic
    (totallyComplexQuasiSplitCyclicTrialitarian_of_cubicSplitTorus htorus)

end Langlands.GroupScheme
