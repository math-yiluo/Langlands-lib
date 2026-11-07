import Langlands.GroupScheme.Rational.VectorPointLieEquiv
import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates

/-! # Naturality of the point-to-Lie comparison under weight isomorphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
    {n : ℕ}
    (e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ V.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)))
    (he : IsNaturalVectorCoordinates e)

omit [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] in
/-- Vector coordinates pulled back between two possibly different group schemes. -/
def vectorCoordinatesAlongIso (ψ : U ≅ V) :
    ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)) :=
  fun X => ((yonedaGrp.mapIso ψ).app (op X)).groupIsoToMulEquiv.trans (e X)

include he in
omit [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] in
/-- Natural vector coordinates pull back along an actual group-scheme isomorphism. -/
theorem IsNaturalVectorCoordinates.alongIso (ψ : U ≅ V) :
    IsNaturalVectorCoordinates (vectorCoordinatesAlongIso e ψ) := by
  intro X Y f x
  change (e Y ((f ≫ x) ≫ ψ.hom.hom.hom)).toAdd = _
  rw [Category.assoc]
  exact he X Y f _

/-- Pulling back the coordinates makes the point-to-Lie comparison commute
with the actual differential of the isomorphism. -/
theorem vectorPointLieEquiv_iso (ψ : U ≅ V)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Additive (Lie.AffinePoints U A)) :
    Lie.targetMapLinear ψ.hom A
        (vectorPointLieEquiv (vectorCoordinatesAlongIso e ψ) (he.alongIso e ψ) A v) =
      vectorPointLieEquiv e he A (Additive.ofMul (v.toMul ≫ ψ.hom.hom.hom)) := by
  apply (vectorLieCoordinates e he A).injective
  rw [vectorLieCoordinates_vectorPointLieEquiv]
  change vectorLieCoordinates (vectorCoordinatesAlongIso e ψ)
      (he.alongIso e ψ) A
      (vectorPointLieEquiv (vectorCoordinatesAlongIso e ψ) (he.alongIso e ψ) A v) = _
  rw [vectorLieCoordinates_vectorPointLieEquiv]
  rfl

variable {e he}

/-- For the same nonzero split-torus weight, any equivariant isomorphism
intertwines the point-to-Lie comparisons without matching their coordinates. -/
theorem vectorPointLieEquiv_equivariantIso
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp U} {c : AutomorphicAction S.toGrp V}
    {a : characterLattice S} (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    {m : ℕ} {eU : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin m → Γ(X.left, ⊤))}
    (hwU : IsWeightVectorCoordinates b a eU) (hwV : IsWeightVectorCoordinates c a e)
    (ψ : U ≅ V)
    (hψ : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ S.X) (x : X ⟶ U.X),
      b.act s x ≫ ψ.hom.hom.hom = c.act s (x ≫ ψ.hom.hom.hom))
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Additive (Lie.AffinePoints U A)) :
    Lie.targetMapLinear ψ.hom A (vectorPointLieEquiv eU hwU.1 A v) =
      vectorPointLieEquiv e hwV.1 A (Additive.ofMul (v.toMul ≫ ψ.hom.hom.hom)) := by
  have hw := hwV.of_equivariantIso ψ hψ
  rw [vectorPointLieEquiv_eq_of_weight hS ha hwU hw]
  exact vectorPointLieEquiv_iso e hwV.1 ψ A v

end Langlands.GroupScheme.RelativeRoot
