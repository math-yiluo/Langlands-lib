import Langlands.VirtualRepresentation.Weil.Local
import Langlands.VirtualRepresentation.Weil.Realization

/-! # Actual local Weil realization and finite induced-character lattices -/

noncomputable section

universe uF uV uQ

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Realize actual local irreducible combinations in the split representation group. -/
def realizeVirtual :
    Lattice.{uF, uV} F →ₗ[ℤ] FiniteRep.VirtualRep ℂ (localWeilGroup F) :=
  Weil.realizeVirtual (localWeilGroup F)

/-- The actual trace character of a local irreducible integral combination. -/
def traceCharacter : Lattice.{uF, uV} F →ₗ[ℤ] (localWeilGroup F → ℂ) :=
  Weil.traceCharacter (localWeilGroup F)

/-- The genuine image of the local trace map, without faithfulness assumptions. -/
def traceImage : Submodule ℤ (localWeilGroup F → ℂ) :=
  LinearMap.range (traceCharacter.{uF, uV} F)

/-- The trace map with its actual image as codomain. -/
def realizeTrace : Lattice.{uF, uV} F →ₗ[ℤ] traceImage.{uF, uV} F :=
  (traceCharacter F).rangeRestrict

/-- The local trace map on the specified unitary lattice. -/
def unitaryTraceCharacter : UnitaryLattice.{uF, uV} F →ₗ[ℤ] (localWeilGroup F → ℂ) :=
  (traceCharacter F).comp (includeUnitary F)

section FiniteMap

variable {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup F.Carrier →* Q)

/-- Pull an actual absolute Galois homomorphism back to the actual Weil group.
No continuity or surjectivity of the supplied finite map is silently assumed. -/
def finiteMap : localWeilGroup F →* Q :=
  q.comp (localProjection F).toMonoidHom

/-- A genuinely induced finite-group representation, pulled back to the actual
local Weil group through the absolute Galois projection. -/
def inflatedMonomial (d : FiniteRep.MonomialDatum ℂ Q) :
    FiniteRep.VirtualRep ℂ (localWeilGroup F) :=
  Weil.inflatedMonomial (localWeilGroup F) (finiteMap F q) d

/-- The integral span of these actual local virtual classes. -/
def inflatedMonomialSpan : Submodule ℤ (FiniteRep.VirtualRep ℂ (localWeilGroup F)) :=
  Weil.inflatedMonomialSpan (localWeilGroup F) (finiteMap F q)

/-- The character image of the actual local induced span. -/
def inflatedInducedCharacters : Submodule ℤ (localWeilGroup F → ℂ) :=
  Weil.inflatedInducedCharacters (localWeilGroup F) (finiteMap F q)

/-- A specified inducing datum gives an element of the actual generated span. -/
def monomialGenerator (d : FiniteRep.MonomialDatum ℂ Q) :
    inflatedMonomialSpan F q :=
  Weil.monomialGenerator (localWeilGroup F) (finiteMap F q) d

/-- Integral combinations of actual inducing data evaluate in that span. -/
def evaluateMonomials :
    IntegralLattice (FiniteRep.MonomialDatum ℂ Q) →ₗ[ℤ] inflatedMonomialSpan F q :=
  Weil.evaluateMonomials (localWeilGroup F) (finiteMap F q)

/-- The irreducible-lattice preimage of the genuine virtual induced span. -/
def inducedVirtualPreimage : Submodule ℤ (Lattice.{uF, uV} F) :=
  (inflatedMonomialSpan F q).comap (realizeVirtual F)

/-- The separate character-level preimage, without an injectivity assumption. -/
def inducedTracePreimage : Submodule ℤ (Lattice.{uF, uV} F) :=
  (inflatedInducedCharacters F q).comap (traceCharacter F)

/-- Restrict the virtual induced preimage to the actual unitary lattice. -/
def unitaryInducedVirtualPreimage : Submodule ℤ (UnitaryLattice.{uF, uV} F) :=
  (inducedVirtualPreimage F q).comap (includeUnitary F)

/-- Restrict the character induced preimage to the actual unitary lattice. -/
def unitaryInducedTracePreimage : Submodule ℤ (UnitaryLattice.{uF, uV} F) :=
  (inducedTracePreimage F q).comap (includeUnitary F)

/-- The local induced trace is the actual finite induced trace pulled back
along the actual local projection and the supplied absolute Galois map. -/
theorem inflatedMonomial_character (d : FiniteRep.MonomialDatum ℂ Q)
    (w : localWeilGroup F) :
    FiniteRep.virtualCharacter (k := ℂ) (G := localWeilGroup F)
      (inflatedMonomial F q d) w =
      FiniteRep.inducedCharacter d (q (localProjection F w)) := by
  change FiniteRep.virtualCharacter (k := ℂ) (G := localWeilGroup F)
    (FiniteRep.virtualRestrict (finiteMap F q)
      (FiniteRep.ofClass (FiniteRep.induce d.1
        (FiniteRep.classOf (FiniteRep.oneDimensional d.2))))) w = _
  rw [FiniteRep.virtualCharacter_restrict, FiniteRep.virtualCharacter_ofClass]
  rfl

/-- Realization in the virtual induced span implies realization in its trace
image; the reverse inclusion is deliberately not assumed. -/
theorem inducedVirtualPreimage_le_trace :
    inducedVirtualPreimage.{uF, uV, uQ} F q ≤ inducedTracePreimage F q := by
  intro x hx
  exact ⟨realizeVirtual F x, hx, rfl⟩

end FiniteMap

end Langlands.VirtualRepresentation.LocalWeil
