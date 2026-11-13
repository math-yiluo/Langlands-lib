import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-! # The unitary lattice field-transport relabelling identity -/

noncomputable section

universe uF uE uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- The unitary lattice pullback along `f` relabels multiplicities. -/
theorem unitaryLatticeEquiv_eq_equivMapDomain (y : UnitaryLattice.{uE, uV} E) :
    unitaryLatticeEquiv F E f y = Finsupp.equivMapDomain (unitaryBasisEquiv F E f) y :=
  rfl

end Langlands.VirtualRepresentation.PadicSupercuspidal
