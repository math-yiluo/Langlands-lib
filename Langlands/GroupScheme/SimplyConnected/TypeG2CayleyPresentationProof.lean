import Langlands.GroupScheme.SimplyConnected.TypeG2CayleyPresentationReduction
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Pinning

/-! # Actual Cayley presentations of type-`G₂` group schemes: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Type-`G₂` groups are Cayley automorphism groups.** Every simply connected,
absolutely almost-simple, affine group scheme of locally finite type over a field, whose
actual Cartan matrix is `G₂` under a numbering of its simple vertices, admits a closed
immersion into `GL₈` realizing exactly the automorphism functor of an actual Cayley datum on
every test scheme. -/
theorem typeG2CayleyPresentation : TypeG2CayleyPresentationStatement.{u} :=
  typeG2CayleyPresentation_of_splitCayleyAutomorphismPinning splitCayleyAutomorphismPinning

end Langlands.GroupScheme
