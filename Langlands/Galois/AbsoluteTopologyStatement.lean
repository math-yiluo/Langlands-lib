import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-! # Compactness of the actual absolute Galois group -/

namespace Langlands.GaloisRepresentation

universe u

/-- The automorphism group of the full algebraic closure is compact in its
existing Krull topology, for every field. -/
def AbsoluteGaloisGroupCompactness : Prop :=
  ∀ (K : Type u) [Field K], CompactSpace (Field.absoluteGaloisGroup K)

end Langlands.GaloisRepresentation
