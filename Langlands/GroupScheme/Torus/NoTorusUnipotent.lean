import Langlands.GroupScheme.Torus.NoTorusStructuralReductionProof
import Langlands.GroupScheme.Torus.FiniteFieldGeometricMaximalProof
import Langlands.GroupScheme.Nilpotent.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.NoCocharacterUnipotent
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningProof
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReduction

/-! # A connected group variety without tori is unipotent -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected affine group over any field is unipotent if every
homomorphism from a torus over that field has trivial range. -/
theorem noTorusUnipotent : NoTorusUnipotentStatement.{u} :=
  noTorusStructuralReduction nilpotentCentralTorus finiteFieldGeometricMaximalTorus
    algClosedTrivialMaximalTorusUnipotent Lie.semisimpleCentralizerSmooth
    Lie.semisimpleCentralizerSpanning semisimpleIsogenyReduction

end Langlands.GroupScheme
