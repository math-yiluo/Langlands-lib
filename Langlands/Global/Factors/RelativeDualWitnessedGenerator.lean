import Langlands.Global.Factors.RelativeLocalOperationTransport
import Langlands.Automorphic.CuspidalContragredientStatement
import Langlands.Automorphic.AssociatedContragredientStatement

/-! # Actual duals of relative witnessed generators -/

noncomputable section

universe uF uW uP

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Automorphic

variable {F E : Type uF} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] {c : FundamentalClass.ClassFamily.{uF}}
  {v : FinitePlace F} [CompactSpace (AdeleQuotient F)]

namespace WitnessedGenerator

variable (d : WitnessedGenerator.{uF, uW, uP} F E c v)
  (hcentral : RelativeWeilGroup.HasUnitaryCentralCharacter d.cuspidal)
  (hex : CuspidalUnitaryContragredientExistenceStatement.{uF})
  (hpres : CuspidalContragredientPresentationExistenceStatement.{uF, uP, uP})
  (hlocal : CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uP})
  (hassoc : RelativeWeilGroup.PresentedContragredientAssociationStatement.{uF, uW, uP, uP})

include hcentral hex hpres hlocal hassoc

set_option maxHeartbeats 600000 in
/-- The actual cuspidal and local contragredient interfaces transport a witnessed
pair, together with its original local map and unitary central character. -/
theorem exists_dual :
    ∃ d' : WitnessedGenerator.{uF, uW, uP} F E c v,
      d'.weil = d.weil.dual ∧
      d'.weilElement = LocalWeil.unitaryDualLatticeEquiv (padicField v) d.weilElement ∧
      d'.automorphicElement = PadicSupercuspidal.unitaryContragredientLatticeEquiv
        (padicField v) d.automorphicElement ∧
      d'.localMap = d.localMap ∧
      RelativeWeilGroup.HasUnitaryCentralCharacter d'.cuspidal := by
  obtain ⟨T', hT', hcentral'⟩ := hex F d.rankIndex d.cuspidal hcentral
  obtain ⟨P', hP'⟩ := hpres F d.rankIndex d.cuspidal T' hcentral hT' d.presentation
  have ha := hassoc c F E d.weil d.cuspidal T' d.presentation P' hT' d.associated
  let := (padicField v).canonicalTopologicalData.topology
  let : TopologicalSpace (GeneralLinear (d.rankIndex + 1) (padicField v).Carrier) :=
    (padicField v).canonicalGeneralLinearTopology _
  let := (padicField v).canonicalGeneralLinearTopologicalGroup (d.rankIndex + 1)
  obtain ⟨e⟩ := hlocal F d.rankIndex d.cuspidal T' hT' d.presentation P' v
    d.local_irreducible d.local_admissible (hP' v).1 (hP' v).2
  have hs : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v)
      ((P'.localComponent v).padicObject (hP' v).1 (hP' v).2).obj
      (PadicSupercuspidal.unitaryContragredientLatticeEquiv (padicField v)
        d.automorphicElement) := by
    apply (PadicSupercuspidal.isUnitaryLatticeSupport_contragredient
      (padicField v) d.automorphic_support).of_iso
    refine SmoothRep.mkIso ?_
    exact e.symm
  refine ⟨
    { rankIndex := d.rankIndex
      weil := d.weil.dual
      weil_irreducible := (FiniteRepresentation.isIrreducible_dual_iff d.weil).mpr
        d.weil_irreducible
      weil_unitary := FiniteRepresentation.isUnitary_dual d.weil d.weil_unitary
      cuspidal := T'
      presentation := P'
      associated := ha
      placeOver := d.placeOver
      reciprocity := d.reciprocity
      localMap := d.localMap
      localMap_spec := d.localMap_spec
      local_irreducible := (hP' v).1
      local_admissible := (hP' v).2
      weilElement := LocalWeil.unitaryDualLatticeEquiv (padicField v) d.weilElement
      weil_effective := (LocalWeil.effective_unitaryDual_iff (padicField v)
        d.weilElement).mpr d.weil_effective
      weil_expansion := localExactExpansion_dual F E c v d.weil d.associated.1 ha.1
        d.localMap d.weilElement d.weil_expansion
      automorphicElement := PadicSupercuspidal.unitaryContragredientLatticeEquiv
        (padicField v) d.automorphicElement
      automorphic_support := hs }, rfl, rfl, rfl, rfl, hcentral'⟩

/-- Choose the actual global dual generator constructed by `exists_dual`. -/
def dual : WitnessedGenerator.{uF, uW, uP} F E c v :=
  Classical.choose (d.exists_dual hcentral hex hpres hlocal hassoc)

@[simp]
theorem dual_weil :
    (d.dual hcentral hex hpres hlocal hassoc).weil = d.weil.dual :=
  (Classical.choose_spec (d.exists_dual hcentral hex hpres hlocal hassoc)).1

@[simp]
theorem dual_weilElement :
    (d.dual hcentral hex hpres hlocal hassoc).weilElement =
      LocalWeil.unitaryDualLatticeEquiv (padicField v) d.weilElement :=
  (Classical.choose_spec (d.exists_dual hcentral hex hpres hlocal hassoc)).2.1

@[simp]
theorem dual_automorphicElement :
    (d.dual hcentral hex hpres hlocal hassoc).automorphicElement =
      PadicSupercuspidal.unitaryContragredientLatticeEquiv (padicField v)
        d.automorphicElement :=
  (Classical.choose_spec (d.exists_dual hcentral hex hpres hlocal hassoc)).2.2.1

@[simp]
theorem dual_localMap :
    (d.dual hcentral hex hpres hlocal hassoc).localMap = d.localMap :=
  (Classical.choose_spec (d.exists_dual hcentral hex hpres hlocal hassoc)).2.2.2.1

/-- The chosen actual dual retains a unitary central character. -/
theorem dual_hasUnitaryCentralCharacter :
    RelativeWeilGroup.HasUnitaryCentralCharacter
      (d.dual hcentral hex hpres hlocal hassoc).cuspidal :=
  (Classical.choose_spec (d.exists_dual hcentral hex hpres hlocal hassoc)).2.2.2.2

end WitnessedGenerator

end Langlands.VirtualRepresentation.RelativeGlobal
