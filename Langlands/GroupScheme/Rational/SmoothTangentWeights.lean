import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Rational.SurjectiveTangentWeights

/-! # Intrinsic weight quotients for smooth equivariant homomorphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
    (b : AutomorphicAction S.toGrp H) (d : AutomorphicAction S.toGrp G)
    (hS : IsSplitTorus S.toGrp) (q : H ⟶ G)
    (hqd : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      b.act s x ≫ q.hom.hom = d.act s (x ≫ q.hom.hom))
    (hq : Smooth q.hom.hom.left)

include hS hqd hq

/-- A smooth equivariant homomorphism maps every intrinsic character space
onto the corresponding target character space. -/
theorem map_actionWeightSpace_eq_of_smooth (χ : characterLattice S) :
    (actionWeightSpace b χ).map (Lie.targetMapLinear q k) = actionWeightSpace d χ :=
  map_actionWeightSpace_eq_of_surjective b d hS q hqd
    (Lie.targetMapLinear_surjective_of_smooth q k hq) χ

/-- Smoothness implies surjectivity of the actual restricted differential. -/
theorem actionWeightSpaceMap_surjective_of_smooth (χ : characterLattice S) :
    Function.Surjective (actionWeightSpaceMap d b q hqd χ) :=
  actionWeightSpaceMap_surjective b d hS q hqd
    (Lie.targetMapLinear_surjective_of_smooth q k hq) χ

/-- The intrinsic character space in the target of a smooth equivariant
homomorphism is the corresponding source space modulo its differential kernel. -/
def smoothActionWeightSpaceQuotientEquiv (χ : characterLattice S) :
    ((actionWeightSpace b χ) ⧸ LinearMap.ker (actionWeightSpaceMap d b q hqd χ)) ≃ₗ[k]
      actionWeightSpace d χ :=
  actionWeightSpaceQuotientEquiv b d hS q hqd
    (Lie.targetMapLinear_surjective_of_smooth q k hq) χ

/-- Absence of any intrinsic character weight descends along a smooth
equivariant homomorphism. -/
theorem actionWeightSpace_eq_bot_of_smooth (χ : characterLattice S)
    (hχ : actionWeightSpace b χ = ⊥) : actionWeightSpace d χ = ⊥ :=
  actionWeightSpace_eq_bot_of_surjective b d hS q hqd
    (Lie.targetMapLinear_surjective_of_smooth q k hq) χ hχ

/-- Every full semigroup weight span maps onto the corresponding target span
under the differential of a smooth equivariant homomorphism. -/
theorem map_semigroupWeightSpan_eq_of_smooth
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupWeightSpan b A).map (Lie.targetMapLinear q k) =
      semigroupWeightSpan d A :=
  map_semigroupWeightSpan_eq_of_surjective b d hS q hqd
    (Lie.targetMapLinear_surjective_of_smooth q k hq) A

end Langlands.GroupScheme.RelativeRoot
