import Langlands.Global.Factors.RelativeIsometryOperationStatement
import Langlands.Global.Factors.RelativeWitnessedDualClosure
import Langlands.Global.Factors.RelativeWitnessedTwistClosure
import Langlands.VirtualRepresentation.Global.RelativeTrivialGenerator
import Langlands.Correspondence.RankOneOperationCompatibility
import Langlands.ClassField.Global.LocalRelativeWeilMapStatement
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement

/-!
# Reduction of relative isometry operations to witnessed generators

This module defines rank-one witnessed realization and reduces the target to
actual dual and twisted generators and a characterized local-map family. Every
global existence and comparison prerequisite remains an explicit proof input.
It does not prove the unconditional `RelativeIsometryOperationStatement`.
-/

noncomputable section

universe uF uW uP

set_option backward.isDefEq.respectTransparency false

namespace Langlands.VirtualRepresentation.LocalWeil

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

theorem twistLatticeEquiv_rankOne_one
    (e : Correspondence.ReciprocityCandidate K) (χ : Correspondence.QuasiCharacter K) :
    twistLatticeEquiv K (LocalFactor.RankOne.weilCharacter K e χ)
        (generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uF, uW} K e 1⟩ :
          Basis.{uF, uW} K)) =
      generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uF, uW} K e χ⟩ :
        Basis.{uF, uW} K) := by
  rw [twistLatticeEquiv_generator]
  congr 1
  change (⟨1, FiniteRepresentation.continuousIrreducibleTwistEquiv
    (LocalFactor.RankOne.weilCharacter K e χ) 1
    (Correspondence.rankOneWeilCharacterClass.{uF, uW} K e 1)⟩ : Basis.{uF, uW} K) = _
  congr 1
  have h := Correspondence.IsRankOneWeilCharacter.twist K
    (Correspondence.rankOneWeilCharacterClass_spec.{uF, uW} K e 1)
    (LocalFactor.RankOne.weilCharacter K e χ)
  have he :
      (LocalFactor.RankOne.weilCharacter K e χ).toMonoidHom *
        (LocalFactor.RankOne.weilCharacter K e 1).toMonoidHom =
      (LocalFactor.RankOne.weilCharacter K e χ).toMonoidHom := by
    ext g
    change _ * (1 : ℂ) = _
    exact mul_one _
  have hh := Eq.mp
    (congrArg (fun η : Weil.Local.localWeilGroup K →* ℂˣ =>
      Correspondence.IsRankOneWeilCharacter K η
        (FiniteRepresentation.continuousIrreducibleTwistEquiv
          (LocalFactor.RankOne.weilCharacter K e χ) 1
          (Correspondence.rankOneWeilCharacterClass.{uF, uW} K e 1))) he) h
  exact Correspondence.IsRankOneWeilCharacter.class_unique K hh
    (Correspondence.rankOneWeilCharacterClass_spec K e χ)

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

theorem supercuspidalTwist_rankOne_one (χ : QuasiCharacter K) :
    supercuspidalTwist K χ (rankOneSupercuspidalClass.{uF, uF} K 1) =
      rankOneSupercuspidalClass.{uF, uF} K χ := by
  have hχ' : IsRankOneCharacter K (χ * 1)
      (supercuspidalToAutomorphic K (rankOneSupercuspidalClass.{uF, uF} K χ)) :=
    Eq.mpr (congrArg (fun η : QuasiCharacter K => IsRankOneCharacter K η
      (supercuspidalToAutomorphic K (rankOneSupercuspidalClass.{uF, uF} K χ)))
      (mul_one χ)) (rankOneSupercuspidalClass_spec K χ)
  have htw : IsSupercuspidalCharacterTwist K χ
      (rankOneSupercuspidalClass.{uF, uF} K 1) (rankOneSupercuspidalClass.{uF, uF} K χ) :=
    IsRankOneCharacter.characterTwist K (rankOneSupercuspidalClass_spec K 1) hχ'
  exact ((isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist K χ _ _).mp htw).symm

end Langlands.Correspondence

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] (c : FundamentalClass.ClassFamily.{uF})

/-- The two exact class-field existence inputs construct all local-map data at an
arithmetic class family. Neither existence input is asserted here. -/
def localMapFamilyOfClassField
    (hrec : Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{uF})
    (hmap : Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{uF})
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c) : RelativeLocalMapFamily F E c := by
  have H : ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      ∃ (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
        (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
        RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι := by
    obtain ⟨I, hI, hd⟩ := hc
    intro v w
    let : w.1.asIdeal.LiesOver v.asIdeal := w.2
    obtain ⟨e, he, _⟩ := hrec _ (towerPadicField v w.1)
      (towerPadicField v w.1).canonicalTopologicalData
    obtain ⟨ι, hι⟩ := hmap I hI c hd F E v w.1 e he
    exact ⟨e, ι, hι⟩
  choose e ι hι using H
  exact ⟨e, ι, hι⟩

end Langlands.VirtualRepresentation.RelativeGlobal

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- A rank-one witnessed generator with the specified local classes. -/
def RelativeWitnessedCharacterRealization
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter (padicField v)) : Prop :=
  ∃ d : WitnessedGenerator.{uF, uW, uP} F E c v,
    LocalWeil.includeUnitary (padicField v) d.weilElement =
        generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uF, uW}
          (padicField v) e χ⟩ : LocalWeil.Basis.{uF, uW} (padicField v)) ∧
      PadicSupercuspidal.includeUnitary (padicField v) d.automorphicElement =
        generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uF}
          (padicField v) χ⟩ : PadicSupercuspidal.Basis.{uF, uF} (padicField v))

/-- The actual trivial generator and witnessed twist closure supply every rank-one
character generator. The local-map family remains an explicit prerequisite. -/
theorem relativeWitnessedCharacterRealization_of_twist
    (M : RelativeLocalMapFamily F E c)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter (padicField v))
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (htwist : RelativeWitnessedTwistClosure.{uF, uW, uP} F E c v e χ hχ) :
    RelativeWitnessedCharacterRealization.{uF, uW, uP} F E c v e χ := by
  obtain ⟨d, hw, ha⟩ := htwist (trivialWitnessedGenerator.{uF, uW, uP} F E c v M)
  refine ⟨d, ?_, ?_⟩
  · rw [hw, LocalWeil.unitaryFieldCharacterTwistLatticeEquiv,
      LocalWeil.includeUnitary_twist, trivialWitnessedGenerator_weil_include]
    exact LocalWeil.twistLatticeEquiv_rankOne_one (padicField v) e χ
  · let K := padicField v
    let := K.canonicalTopologicalData.topology
    rw [ha]
    change Supercuspidal.includeUnitary K.Carrier
      (Supercuspidal.unitaryTwistLatticeEquiv
        (fun n => Correspondence.determinantQuasiCharacter K n χ) _ _ _
        (trivialWitnessedGenerator.{uF, uW, uP} F E c v M).automorphicElement) = _
    rw [Supercuspidal.includeUnitary_twist]
    have hinc := trivialWitnessedGenerator_automorphic_include.{uF, uW, uP} F E c v M
    change Supercuspidal.includeUnitary K.Carrier
      (trivialWitnessedGenerator.{uF, uW, uP} F E c v M).automorphicElement = _ at hinc
    rw [hinc, Supercuspidal.twistLatticeEquiv_generator]
    change generator (⟨1, Correspondence.supercuspidalTwist K χ
      (Correspondence.rankOneSupercuspidalClass.{uF, uF} K 1)⟩ :
        PadicSupercuspidal.Basis.{uF, uF} K) = _
    rw [Correspondence.supercuspidalTwist_rankOne_one]

variable
  (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
    automorphicImage.{uF, uW, uP} F E c v)
  (hT : RelativeGeneratedPositiveIsometry F E c v T)

include hT

/-- Every witnessed integral pair lies on the graph of a generator-fixing map. -/
theorem relative_pair_on_graph
    {z : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)}
    (hz : z ∈ pairedLattice.{uF, uW, uP} F E c v) :
    ∃ x : weilImage.{uF, uW, uP} F E c v, x.1 = z.1 ∧ (T x).1 = z.2 := by
  let G := (weilImage.{uF, uW, uP} F E c v).subtype.prod
    ((automorphicImage.{uF, uW, uP} F E c v).subtype.comp T.toLinearMap)
  have hgraph : pairedLattice.{uF, uW, uP} F E c v ≤ LinearMap.range G := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    refine ⟨⟨d.weilElement, witnessed_weil_mem d⟩, ?_⟩
    exact Prod.ext rfl (congrArg Subtype.val (hT.1 d))
  obtain ⟨x, hx⟩ := hgraph hz
  exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

/-- Each input and its image form an actual pair in the generated paired span. -/
theorem relative_graph_mem_pair
    (x : weilImage.{uF, uW, uP} F E c v) :
    (x.1, (T x).1) ∈ pairedLattice.{uF, uW, uP} F E c v := by
  obtain ⟨y, hy⟩ := exists_pair_of_mem_weilImage x.property
  obtain ⟨x', hx', hTx'⟩ := relative_pair_on_graph F E c v T hT hy
  have heq : x' = x := Subtype.ext hx'
  rw [heq] at hTx'
  simpa only [hTx'] using hy

/-- Linearity extends compatible witnessed generator operations to the span. -/
theorem relative_operation_of_witnessed
    (A : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) →ₗ[ℤ]
      LocalWeil.UnitaryLattice.{uF, uW} (padicField v))
    (B : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v) →ₗ[ℤ]
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v))
    (hAB : ∀ d : WitnessedGenerator.{uF, uW, uP} F E c v,
      ∃ d' : WitnessedGenerator.{uF, uW, uP} F E c v,
        d'.weilElement = A d.weilElement ∧
          d'.automorphicElement = B d.automorphicElement)
    (x : weilImage.{uF, uW, uP} F E c v) :
    ∃ h : A x.1 ∈ weilImage.{uF, uW, uP} F E c v,
      (T ⟨_, h⟩).1 = B (T x).1 := by
  let P := pairedLattice.{uF, uW, uP} F E c v
  let op := A.prodMap B
  have hclosed : P ≤ P.comap op := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    obtain ⟨d', hw, ha⟩ := hAB d
    change (A d.weilElement, B d.automorphicElement) ∈ P
    rw [← hw, ← ha]
    exact witnessed_pair_mem d'
  have hpair := hclosed (relative_graph_mem_pair F E c v T hT x)
  obtain ⟨z, hz, hTz⟩ := relative_pair_on_graph F E c v T hT hpair
  change z.1 = A x.1 at hz
  change (T z).1 = B (T x).1 at hTz
  have hmem : A x.1 ∈ weilImage.{uF, uW, uP} F E c v := hz ▸ z.property
  refine ⟨hmem, ?_⟩
  have heq : (⟨A x.1, hmem⟩ : weilImage.{uF, uW, uP} F E c v) = z :=
    Subtype.ext hz.symm
  rwa [heq]

/-- Conditional assembly; each generator construction remains to be proved. -/
theorem relativeIsometryOperations_of_witnessed
    (hdual : RelativeWitnessedDualClosure.{uF, uW, uP} F E c v)
    (htwist : ∀ (e : Correspondence.ReciprocityCandidate (padicField v)),
      Correspondence.IsGeometricReciprocity (padicField v) e →
      ∀ (χ : Correspondence.QuasiCharacter (padicField v))
        (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
        RelativeWitnessedTwistClosure.{uF, uW, uP} F E c v e χ hχ)
    (hchar : ∀ (e : Correspondence.ReciprocityCandidate (padicField v)),
      Correspondence.IsGeometricReciprocity (padicField v) e →
      ∀ (χ : Correspondence.QuasiCharacter (padicField v))
        (_hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
        RelativeWitnessedCharacterRealization.{uF, uW, uP} F E c v e χ) :
    RelativeIsometryOperations F E c v T := by
  constructor
  · exact relative_operation_of_witnessed F E c v T hT
      (LocalWeil.unitaryDualLatticeEquiv (padicField v)).toLinearMap
      (PadicSupercuspidal.unitaryContragredientLatticeEquiv (padicField v)).toLinearMap
      hdual
  · intro e he χ hχ
    constructor
    · exact relative_operation_of_witnessed F E c v T hT
        (LocalWeil.unitaryFieldCharacterTwistLatticeEquiv (padicField v) e χ hχ).toLinearMap
        (PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv (padicField v) χ hχ).toLinearMap
        (htwist e he χ hχ)
    · obtain ⟨d, hw, ha⟩ := hchar e he χ hχ
      refine ⟨⟨d.weilElement, witnessed_weil_mem d⟩, hw, ?_⟩
      rw [hT.1 d]
      exact ha

/-- The constructed trivial generator makes the character clause a consequence
of the actual witnessed twist construction. The two closure inputs and the map
family still need to be supplied from the target's published hypotheses. -/
theorem relativeIsometryOperations_of_dual_twist
    (M : RelativeLocalMapFamily F E c)
    (hdual : RelativeWitnessedDualClosure.{uF, uW, uP} F E c v)
    (htwist : ∀ (e : Correspondence.ReciprocityCandidate (padicField v)),
      Correspondence.IsGeometricReciprocity (padicField v) e →
      ∀ (χ : Correspondence.QuasiCharacter (padicField v))
        (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
        RelativeWitnessedTwistClosure.{uF, uW, uP} F E c v e χ hχ) :
    RelativeIsometryOperations F E c v T :=
  relativeIsometryOperations_of_witnessed F E c v T hT hdual htwist
    (fun e he χ hχ => relativeWitnessedCharacterRealization_of_twist
      F E c v M e χ hχ (htwist e he χ hχ))

/-- Class-field existence inputs discharge the map-family construction. The actual
dual and twisted witnessed-generator constructions still remain explicit. -/
theorem relativeIsometryOperations_of_classField
    (hrec : Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{uF})
    (hmap : Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{uF})
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hdual : RelativeWitnessedDualClosure.{uF, uW, uP} F E c v)
    (htwist : ∀ (e : Correspondence.ReciprocityCandidate (padicField v)),
      Correspondence.IsGeometricReciprocity (padicField v) e →
      ∀ (χ : Correspondence.QuasiCharacter (padicField v))
        (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
        RelativeWitnessedTwistClosure.{uF, uW, uP} F E c v e χ hχ) :
    RelativeIsometryOperations F E c v T :=
  relativeIsometryOperations_of_dual_twist F E c v T hT
    (localMapFamilyOfClassField F E c hrec hmap hc) hdual htwist

/-- The concrete dual and twist constructions discharge the two witnessed
closure predicates. Every global existence and comparison prerequisite is
still an explicit proof input of this intermediate theorem. -/
theorem relativeIsometryOperations_of_globalInputs
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hrec : Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{uF})
    (hmap : Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{uF})
    (hcentral : RelativeWeilGroup.AssociatedCentralCharacterStatement.{uF, uW, uP})
    (hdual : Langlands.Automorphic.CuspidalUnitaryContragredientExistenceStatement.{uF})
    (hdualpres : Langlands.Automorphic.CuspidalContragredientPresentationExistenceStatement.{uF, uP, uP})
    (hduallocal : Langlands.Automorphic.CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uP})
    (hdualassoc : RelativeWeilGroup.PresentedContragredientAssociationStatement.{uF, uW, uP, uP})
    (htwist : Langlands.Automorphic.CuspidalDeterminantMultipleStatement.{uF, uP})
    (htwistassoc : RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement.{uF, uW, uP, uP})
    (htransfer : RelativeWeilGroup.LocalTransferReciprocityStatement.{uF})
    (hextend : ∀ η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ,
      (∀ a, ‖(η a : ℂ)‖ = 1) →
      ∃ Ω : HeckeCharacter F, Ω.IsUnitary ∧ Ω.finiteComponent v = η) :
    RelativeIsometryOperations F E c v T := by
  apply relativeIsometryOperations_of_classField F E c v T hT hrec hmap hc
  · exact relativeWitnessedDualClosure_of_centralComparison
      F E c v hc hcentral hdual hdualpres hduallocal hdualassoc
  · intro e he χ hχ
    exact relativeWitnessedTwistClosure_of_globalInputs
      F E c v hc htwist htwistassoc htransfer hextend e he χ hχ

end Langlands.Global.PoleComparison

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global

/-- Full-universe reduction of the exact target. This is deliberately conditional:
none of the eleven global proof inputs is asserted by this theorem. -/
theorem relativeIsometryOperationStatement_of_globalInputs
    (hrec : Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{uF})
    (hmap : Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{uF})
    (hcentral : RelativeWeilGroup.AssociatedCentralCharacterStatement.{uF, uW, uP})
    (hdual : Langlands.Automorphic.CuspidalUnitaryContragredientExistenceStatement.{uF})
    (hdualpres : Langlands.Automorphic.CuspidalContragredientPresentationExistenceStatement.{uF, uP, uP})
    (hduallocal : Langlands.Automorphic.CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uP})
    (hdualassoc : RelativeWeilGroup.PresentedContragredientAssociationStatement.{uF, uW, uP, uP})
    (htwist : Langlands.Automorphic.CuspidalDeterminantMultipleStatement.{uF, uP})
    (htwistassoc : RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement.{uF, uW, uP, uP})
    (htransfer : RelativeWeilGroup.LocalTransferReciprocityStatement.{uF})
    (hextend : ∀ (F : Type uF) [Field F] [NumberField F] (v : FinitePlace F)
      (η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ),
      (∀ a, ‖(η a : ℂ)‖ = 1) →
      ∃ Ω : HeckeCharacter F, Ω.IsUnitary ∧ Ω.finiteComponent v = η) :
    RelativeIsometryOperationStatement.{uF, uW, uP} := by
  intro F E _ _ _ _ _ _ _ c hc v _ψ _hpole T hT
  exact relativeIsometryOperations_of_globalInputs F E c v T hT hc hrec hmap
    hcentral hdual hdualpres hduallocal hdualassoc htwist htwistassoc htransfer
    (hextend F v)

end Langlands.Global.PoleComparison
