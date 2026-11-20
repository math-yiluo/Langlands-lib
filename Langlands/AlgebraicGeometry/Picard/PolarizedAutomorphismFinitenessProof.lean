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
    (fun k _ _ _ A => homFiniteFree k A A)

end Langlands.AbelianScheme
