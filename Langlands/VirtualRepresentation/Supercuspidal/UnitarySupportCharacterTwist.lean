import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport
import Langlands.VirtualRepresentation.Supercuspidal.UnitaryTwist
import Langlands.Representation.Classification.SupercuspidalSupportCharacterTwist

/-! # Smooth norm-one character twists of actual unitary supports -/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The genuine unitary basis twist for a smooth norm-one field character. -/
def unitarySmoothCharacterTwistBasisEquiv
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1) :
    UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.unitaryTwistBasisEquiv
    (fun _ => χ.toMonoidHom.comp GeneralLinear.determinant)
    (fun n => χ.isOpen_ker.preimage
      (F.canonicalTopologicalData.generalLinearDeterminant n).continuous)
    (fun _ => GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom)
    (fun _ _ => hu _)

/-- The integral extension of the same actual smooth-character basis twist. -/
def unitarySmoothCharacterTwistLatticeEquiv
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1) :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  reindex (unitarySmoothCharacterTwistBasisEquiv F χ hu)

@[simp]
theorem unitarySmoothCharacterTwistLatticeEquiv_generator
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1) (b : UnitaryBasis.{uF, uV} F) :
    unitarySmoothCharacterTwistLatticeEquiv F χ hu (generator b) =
      generator (unitarySmoothCharacterTwistBasisEquiv F χ hu b) :=
  Finsupp.domLCongr_single _ _ _

/-- The smooth character twist of actual unitary cuspidal data. -/
def unitarySmoothCharacterTwistDatum
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1)
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData :=
  (unitaryCuspidalDatumBasisEquiv F).symm
    (unitarySmoothCharacterTwistBasisEquiv F χ hu (unitaryCuspidalDatumBasisEquiv F d))

@[simp]
theorem unitaryCuspidalDatumBasisEquiv_unitarySmoothCharacterTwistDatum
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1)
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    unitaryCuspidalDatumBasisEquiv F (unitarySmoothCharacterTwistDatum F χ hu d) =
      unitarySmoothCharacterTwistBasisEquiv F χ hu (unitaryCuspidalDatumBasisEquiv F d) :=
  (unitaryCuspidalDatumBasisEquiv F).apply_symm_apply _

/-- Forgetting unitarity gives the actual determinant-character datum twist. -/
@[simp]
theorem unitarySmoothCharacterTwistDatum_val
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1)
    (d : UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData) :
    (unitarySmoothCharacterTwistDatum F χ hu d).val = d.val.characterTwist χ := by
  apply (cuspidalDatumBasisEquiv F).injective
  have he := congrArg Subtype.val
    (unitaryCuspidalDatumBasisEquiv_unitarySmoothCharacterTwistDatum F χ hu d)
  exact he

/-- Encoding the transformed multiset is the same integral unitary lattice twist. -/
theorem unitarySupportLattice_smoothCharacterTwist
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1)
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData)) :
    unitarySupportLattice F (s.map (unitarySmoothCharacterTwistDatum F χ hu)) =
      unitarySmoothCharacterTwistLatticeEquiv F χ hu (unitarySupportLattice F s) := by
  induction s using Multiset.induction_on with
  | empty => simp [unitarySupportLattice]
  | cons d s ih =>
    rw [Multiset.map_cons, unitarySupportLattice_cons, unitarySupportLattice_cons,
      map_add, unitarySmoothCharacterTwistLatticeEquiv_generator, ih,
      unitaryCuspidalDatumBasisEquiv_unitarySmoothCharacterTwistDatum]

/-- A supplied actual unitary lattice support transports by a smooth norm-one twist. -/
theorem isUnitaryLatticeSupport_smoothCharacterTwist {n : ℕ}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : UnitaryLattice.{uF, uV} F}
    (hx : IsUnitaryLatticeSupport F π x)
    (χ : letI := F.canonicalTopologicalData.topology
      Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ a, ‖(χ.toMonoidHom a : ℂ)‖ = 1) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    IsUnitaryLatticeSupport F
      (π.twist (χ.toMonoidHom.comp GeneralLinear.determinant)
        (χ.isOpen_ker.preimage
          (F.canonicalTopologicalData.generalLinearDeterminant n).continuous))
      (unitarySmoothCharacterTwistLatticeEquiv F χ hu x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨s.map (unitarySmoothCharacterTwistDatum F χ hu), ?_,
    unitarySupportLattice_smoothCharacterTwist F χ hu s⟩
  simpa only [Multiset.map_map, Function.comp_def, unitarySmoothCharacterTwistDatum_val] using
    hs.characterTwist χ

end Langlands.VirtualRepresentation.PadicSupercuspidal
