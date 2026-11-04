import Langlands.Representation.CuspidalSupport.GroupTransport
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Fixed-vector generation under a group equivalence -/

set_option autoImplicit false

namespace Langlands

/-- Generation by fixed vectors is invariant under pullback along a group
equivalence, with the subgroup transported by the inverse equivalence. -/
def FixedVectorsGroupEquivalenceGenerationStatement.{uR, uG, uH, uV} : Prop :=
  ∀ (R : Type uR) [CommRing R]
    (G : Type uG) [Group G] (H : Type uH) [Group H]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (e : H ≃* G) (K : Subgroup H),
    (∀ S : Subrepresentation (ρ.comp e.toMonoidHom),
      fixedVectors (ρ.comp e.toMonoidHom) K ≤ S.toSubmodule → S = ⊤) ↔
    (∀ S : Subrepresentation ρ,
      fixedVectors ρ (K.comap e.symm.toMonoidHom) ≤ S.toSubmodule → S = ⊤)

end Langlands
