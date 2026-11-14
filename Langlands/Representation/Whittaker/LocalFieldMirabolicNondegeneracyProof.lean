import Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyBridge
import Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracy

/-!
# Absence of degenerate mirabolic submodules over local fields: proof

Theorem 4.9 of Bernstein and Zelevinsky (1977), in the formulation
`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyStatement`, for every nonarchimedean local
field of any characteristic. It combines the all-field theorem
`Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy.mirabolicNondegeneracy` with the
bridge from packaged fields to ambient instances.
-/

namespace Langlands.Whittaker

universe uF uV

/-- **Bernstein–Zelevinsky, Theorem 4.9.** Over every nonarchimedean local field, an irreducible
admissible generic representation of `GL_(n+1)(F)` has no nonzero mirabolic subrepresentation
whose standard full upper-unipotent character quotient vanishes. -/
theorem localFieldMirabolicNondegeneracy :
    LocalFieldMirabolicNondegeneracyStatement.{uF, uV} :=
  LocalFieldMirabolicNondegeneracyBridge.localFieldMirabolicNondegeneracy_of_packaged
    fun _ => Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy.mirabolicNondegeneracy

end Langlands.Whittaker
