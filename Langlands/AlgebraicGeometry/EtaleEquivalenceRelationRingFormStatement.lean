import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The ring form of an étale equivalence relation with affine relation scheme

An étale equivalence relation on an affine scheme `E.U`, whose relation scheme `E.R` is affine and
whose map `j = (t, s) : E.R ⟶ E.U ⨯ E.U` is a closed immersion, gives a
`RingEtaleEquivalenceRelation` on the rings of global sections.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation with `E.U` and `E.R` affine and
`j = (t, s) : E.R ⟶ E.U ⨯ E.U` a closed immersion, then the target map
`E.t.appTop : Γ(E.U, ⊤) ⟶ Γ(E.R, ⊤)`, with `Γ(E.R, ⊤)` a `Γ(E.U, ⊤)`-algebra through the source
map `E.s.appTop`, is a `RingEtaleEquivalenceRelation`. -/
def EtaleEquivalenceRelationRingFormStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsAffine E.R →
    IsClosedImmersion (prod.lift E.t E.s) →
      letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
      RingEtaleEquivalenceRelation E.t.appTop.hom

end Langlands.AlgebraicGeometry
