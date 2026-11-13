import Langlands.Representation.Whittaker.TypeAsymptoticProof
import Langlands.AllField.Representation.Whittaker.FullTorusExtension
import Langlands.AllField.Representation.Whittaker.LastEntryOneAsymptoticProof
/-!
# Full-torus expansion for finite-type Whittaker representations

Apply the full-torus extension to the published last-entry-one theorem.
-/

namespace Langlands.AllField

universe uF uV

/-- The Whittaker-type expansion on the entire diagonal torus, uniformly in
all equivariant functionals and vectors. -/
theorem whittakerTypeAsymptotic : WhittakerTypeAsymptoticStatement.{uF,uV} :=
  Langlands.AllField.WhittakerFullTorus.of_lastEntryOne whittakerLastEntryOneAsymptotic

end Langlands.AllField
