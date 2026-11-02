import Langlands.AlgebraicGeometry.GroupoidCoactionFlat
import Langlands.AlgebraicGeometry.GroupoidCoactionPushout
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationRingQuotient

/-! # The conditional invariant-ring quotient of an affine étale equivalence relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

open GroupoidCoaction

variable (E : EtaleEquivalenceRelation.{u})

local instance sourceAlgebra : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) :=
  E.s.appTop.hom.toAlgebra

variable (hE : RingEtaleEquivalenceRelation E.t.appTop.hom)
variable (hacyclic : E.ComodulesAcyclic)
variable (hdetect : ∀ (K : Type u) [AddCommGroup K] [Module Γ(E.U, ⊤) K]
  (θK : GroupoidCoaction E.t.appTop.hom K),
  Subsingleton θK.invariantSubmodule → Subsingleton K)

/-- The equalizer ring gives a faithfully flat coordinate-ring pushout when all
coactions are acyclic and invariants detect zero coactions. -/
noncomputable def invariantRingQuotient : E.FaithfullyFlatRingQuotient where
  baseRing := CommRingCat.of (invariantRing E.t.appTop.hom)
  inclusion := CommRingCat.ofHom (algebraMap (invariantRing E.t.appTop.hom) Γ(E.U, ⊤))
  faithfullyFlat :=
    faithfullyFlat_invariantRing_algebraMap_of_acyclic hE hacyclic hdetect
  isPushout := isPushout_invariantRing hE hacyclic hdetect

include hE hacyclic hdetect in
/-- The conditional invariant-ring construction gives the published affine quotient
predicate. All rings, modules and schemes lie in the same arbitrary universe. -/
theorem hasAffineQuotient_of_acyclic_of_detects_zero
    [IsAffine E.U] [IsAffine E.R] : E.HasAffineQuotient :=
  (invariantRingQuotient E hE hacyclic hdetect).hasAffineQuotient

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
