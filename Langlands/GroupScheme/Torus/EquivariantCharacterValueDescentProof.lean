import Langlands.GroupScheme.Torus.EquivariantCharacterValueDescentStatement
import Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent

/-! # Galois descent of prescribed torus character values -/

universe u

namespace Langlands.GroupScheme

/-- Every Galois-equivariant homomorphism from the character lattice of a split
base change to the extension's units is evaluation at an original-field point. -/
theorem torusEquivariantCharacterValueDescent :
    TorusEquivariantCharacterValueDescentStatement.{u} :=
  exists_rationalPoint_characterValue_eq_of_equivariant

end Langlands.GroupScheme
