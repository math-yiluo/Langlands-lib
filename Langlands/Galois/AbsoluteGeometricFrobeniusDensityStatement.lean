import Langlands.Galois.CompatibleFamily

/-! # Density of geometric Frobenius conjugacy classes in the absolute Galois group -/

noncomputable section

universe uE

namespace Langlands.GaloisRepresentation

open Langlands.Global

/-- Images of actual local geometric Frobenius lifts away from finitely many
places, together with their global conjugates, are dense for the Krull topology. -/
def AbsoluteGeometricFrobeniusDensityStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] (S : Finset (FinitePlace E)),
    Dense {g : Field.absoluteGaloisGroup E |
      ∃ (v : FinitePlace E) (a : LocalGroup v) (s : Field.absoluteGaloisGroup E),
        v ∉ S ∧ IsGeometricFrobeniusLift v a ∧
          g = s * Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) a * s⁻¹}

end Langlands.GaloisRepresentation
