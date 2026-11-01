import Langlands.Representation.Whittaker.FullTorusExtension
import Langlands.Representation.Whittaker.LastEntryOneAsymptoticProof

/-!
# Full-torus expansion for finite-type Whittaker representations

Apply the full-torus extension to the published last-entry-one theorem.
-/

namespace Langlands

universe uF uV

/-- The Whittaker-type expansion on the entire diagonal torus, uniformly in
all equivariant functionals and vectors. -/
theorem whittakerTypeAsymptotic : WhittakerTypeAsymptoticStatement.{uF,uV} :=
  WhittakerFullTorus.of_lastEntryOne whittakerLastEntryOneAsymptotic

end Langlands
