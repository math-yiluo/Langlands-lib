import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Classification.Supercuspidal

/-!
# Supercuspidal classes in different carrier universes

An actual p-adic general linear group has the same supercuspidal classes in
any two carrier universes. The bijection matches classes with intertwining
equivalences of representatives and preserves unitarizability.
-/

noncomputable section

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

private theorem exists_supercuspidalRepresentative :
    letI := T.topology
    ∀ A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n),
      ∃ B : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n),
        Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  let := T.topology
  intro A
  obtain ⟨σ, hσ, ⟨e⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uV, uW} p F T n A.obj A.property.1
  exact ⟨⟨σ, hσ, isSupercuspidal_of_equiv e A.property.2⟩, ⟨e⟩⟩

private def changeCarrierRep :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n) →
      SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n) :=
  fun A => (exists_supercuspidalRepresentative T A).choose

private def changeCarrierRepEquiv :
    letI := T.topology
    ∀ A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n),
      A.obj.representation.Equiv (changeCarrierRep.{uF, uV, uW} T A).obj.representation :=
  fun A => (exists_supercuspidalRepresentative T A).choose_spec.some

private def changeCarrier :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) →
      GeneralLinear.SupercuspidalClass.{uW, uF} (F := F.Carrier) (n := n) := by
  letI := T.topology
  refine Quotient.map (changeCarrierRep T) ?_
  rintro A B ⟨i⟩
  let e := SmoothRep.equivOfIso (supercuspidalProperty.ι.mapIso i)
  exact ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso
    (((changeCarrierRepEquiv T A).symm.trans e).trans (changeCarrierRepEquiv T B)))⟩

private theorem changeCarrier_changeCarrier :
    letI := T.topology
    ∀ a : GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n),
      changeCarrier.{uF, uW, uV} T (changeCarrier.{uF, uV, uW} T a) = a := by
  let := T.topology
  intro a
  induction a using Quotient.inductionOn with
  | h A =>
    let e := (changeCarrierRepEquiv T A).trans (changeCarrierRepEquiv T (changeCarrierRep T A))
    exact Quotient.sound ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso e.symm)⟩

/-- The class bijection induced by realization in a different carrier universe. -/
def supercuspidalClassCarrierEquiv (n : ℕ) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) ≃
      GeneralLinear.SupercuspidalClass.{uW, uF} (F := F.Carrier) (n := n) where
  toFun := changeCarrier T
  invFun := changeCarrier T
  left_inv := changeCarrier_changeCarrier T
  right_inv := changeCarrier_changeCarrier T

/-- The bijection matches precisely the classes whose representatives are
equivalent as representations of the same general linear group. -/
theorem supercuspidalClassCarrierEquiv_isoClass_eq_iff (n : ℕ) :
    letI := T.topology
    ∀ (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n))
      (B : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n)),
      T.supercuspidalClassCarrierEquiv n A.isoClass = B.isoClass ↔
        Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  let := T.topology
  intro A B
  change (changeCarrierRep T A).isoClass = B.isoClass ↔ _
  rw [SupercuspidalRep.isoClass_eq_iff]
  constructor
  · rintro ⟨i⟩
    exact ⟨(changeCarrierRepEquiv T A).trans
      (SmoothRep.equivOfIso (supercuspidalProperty.ι.mapIso i))⟩
  · rintro ⟨e⟩
    exact ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso ((changeCarrierRepEquiv T A).symm.trans e))⟩

@[simp]
theorem isUnitarizable_supercuspidalClassCarrierEquiv_iff (n : ℕ) :
    letI := T.topology
    ∀ a : GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n),
      (T.supercuspidalClassCarrierEquiv.{uF, uV, uW} n a).IsUnitarizable ↔ a.IsUnitarizable := by
  let := T.topology
  intro a
  induction a using Quotient.inductionOn with
  | h A => exact isUnitarizable_iff_of_equiv (changeCarrierRepEquiv T A).symm

end Langlands.PadicField.TopologicalData
