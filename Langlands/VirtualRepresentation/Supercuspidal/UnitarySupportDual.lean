import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport
import Langlands.VirtualRepresentation.Supercuspidal.Contragredient
import Langlands.Representation.Classification.CuspidalProductContragredient

/-! # Actual contragredients of witnessed unitary supercuspidal supports -/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.PadicField.TopologicalData
open Langlands.Classification.CuspidalProductContragredient

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual datum and lattice models commute with the smooth contragredient. -/
theorem cuspidalDatumBasisEquiv_dualDatum
    (d : CuspidalDatum.{uV, uF} F.canonicalTopologicalData) :
    cuspidalDatumBasisEquiv F (dualDatum d) =
      contragredientBasisEquiv F (cuspidalDatumBasisEquiv F d) := by
  rcases d with ⟨n, hn, c⟩
  change (⟨⟨n, hn⟩,
    dualClass (⟨n, hn, c⟩ : CuspidalDatum.{uV, uF} F.canonicalTopologicalData)⟩ :
      Basis.{uF, uV} F) = _
  rw [dualClass_def]
  rfl

/-- Contragredient on actual unitary data, transported through the genuine basis. -/
def unitaryContragredientDatum
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData :=
  (unitaryCuspidalDatumBasisEquiv F).symm
    (unitaryContragredientBasisEquiv F (unitaryCuspidalDatumBasisEquiv F d))

@[simp]
theorem unitaryCuspidalDatumBasisEquiv_unitaryContragredientDatum
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    unitaryCuspidalDatumBasisEquiv F (unitaryContragredientDatum F d) =
      unitaryContragredientBasisEquiv F (unitaryCuspidalDatumBasisEquiv F d) :=
  (unitaryCuspidalDatumBasisEquiv F).apply_symm_apply _

/-- The transformed datum is the actual smooth-dual datum after forgetting unitarity. -/
@[simp]
theorem unitaryContragredientDatum_val
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    (unitaryContragredientDatum F d).val = dualDatum d.val := by
  apply (cuspidalDatumBasisEquiv F).injective
  have he := congrArg Subtype.val
    (unitaryCuspidalDatumBasisEquiv_unitaryContragredientDatum F d)
  change cuspidalDatumBasisEquiv F (unitaryContragredientDatum F d).val =
    contragredientBasisEquiv F (cuspidalDatumBasisEquiv F d.val) at he
  exact he.trans (cuspidalDatumBasisEquiv_dualDatum F d.val).symm

/-- The datum operation retains the actual involutivity of smooth duality. -/
@[simp]
theorem unitaryContragredientDatum_apply_apply
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    unitaryContragredientDatum F (unitaryContragredientDatum F d) = d := by
  apply Subtype.ext
  simp only [unitaryContragredientDatum_val, dualDatum_dualDatum]

/-- Encoding the transformed multiset agrees with the genuine unitary lattice dual. -/
theorem unitarySupportLattice_contragredient
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData)) :
    unitarySupportLattice F (s.map (unitaryContragredientDatum F)) =
      unitaryContragredientLatticeEquiv F (unitarySupportLattice F s) := by
  induction s using Multiset.induction_on with
  | empty => simp [unitarySupportLattice]
  | cons d s ih =>
    rw [Multiset.map_cons, unitarySupportLattice_cons, unitarySupportLattice_cons,
      map_add, unitaryContragredientLatticeEquiv_generator, ih,
      unitaryCuspidalDatumBasisEquiv_unitaryContragredientDatum]

/-- An actual unitary lattice support dualizes to the actual smooth contragredient. -/
theorem isUnitaryLatticeSupport_contragredient {n : ℕ}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : UnitaryLattice.{uF, uV} F}
    (hx : IsUnitaryLatticeSupport F π x) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    IsUnitaryLatticeSupport F π.contragredient
      (unitaryContragredientLatticeEquiv F x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨s.map (unitaryContragredientDatum F), ?_,
    unitarySupportLattice_contragredient F s⟩
  simpa only [Multiset.map_map, Function.comp_def, unitaryContragredientDatum_val] using
    isSupercuspidalSupport_contragredient hs

end Langlands.VirtualRepresentation.PadicSupercuspidal
