import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphismLattice
import Langlands.AlgebraicGeometry.Picard.RosatiRationalInverseProof
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityProof
import Langlands.AbelianScheme.HomFiniteFreeProof

/-! # Finiteness of the actual integral polarized automorphism group -/

universe u

namespace Langlands.AbelianScheme

/-- The actual integral automorphisms preserving a geometric polarization over
an algebraically closed characteristic-zero field form a finite group. -/
theorem polarizedAutomorphismFiniteness :
    PolarizedAutomorphismFinitenessStatement.{u} :=
  polarizedAutomorphismFiniteness_of_rosati_and_lattice
    Rosati.rationalInverse Rosati.positivity
    (fun k _ _ _ A => by
      obtain ⟨hfree, hfin⟩ := homFiniteFree k A A
      exact ⟨Module.Free.of_equiv CategoryTheory.End.addEquiv.toIntLinearEquiv.symm,
        Module.Finite.equiv CategoryTheory.End.addEquiv.toIntLinearEquiv.symm⟩)

end Langlands.AbelianScheme
