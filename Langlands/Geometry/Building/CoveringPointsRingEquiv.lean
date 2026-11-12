import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.GroupScheme.Rational.RingEquivBaseChange

/-! # Rational point comparison for a covering field isomorphism -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K]

/-- The two rational-section extension conventions agree for a ring equivalence. -/
theorem baseChangeSectionHom_eq_rationalExtend (σ : k ≃+* K)
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    let : Algebra k K := σ.toRingHom.toAlgebra
    baseChangeSectionHom (specMapOfRingEquiv σ) G = rationalExtend k K G := by
  let : Algebra k K := σ.toRingHom.toAlgebra
  exact (rationalExtend_hom_eq_baseChangeSectionHom k K G).symm

/-- The covering map uses the actual rational-extension homomorphism. -/
theorem coveringPointsMap_eq_rationalExtend (σ : k ≃+* K)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G ⟶ H) :
    let : Algebra k K := σ.toRingHom.toAlgebra
    coveringPointsMap σ fG = (rationalPoints.map fG).comp (rationalExtend k K G) := by
  let : Algebra k K := σ.toRingHom.toAlgebra
  rw [coveringPointsMap, baseChangeSectionHom_eq_rationalExtend]

/-- A group-scheme isomorphism covering a field isomorphism is bijective on points. -/
theorem coveringPointsMap_bijective (σ : k ≃+* K)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G ≅ H) :
    Function.Bijective (coveringPointsMap σ fG.hom) := by
  have : IsIso (specMapOfRingEquiv σ) := isIso_SpecMap_iff.mpr σ.bijective
  exact (isoPointsEquiv fG (Over.mk (𝟙 _))).bijective.comp
    (baseChangeSectionHom_bijective_of_isIso _ _)

/-- The actual point equivalence induced by a covering field and group isomorphism. -/
def coveringPointsEquiv (σ : k ≃+* K)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G ≅ H) :
    rationalPoints G ≃* rationalPoints H :=
  MulEquiv.ofBijective (coveringPointsMap σ fG.hom) (coveringPointsMap_bijective σ fG)

@[simp]
theorem coveringPointsEquiv_apply (σ : k ≃+* K)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G ≅ H)
    (g : rationalPoints G) :
    coveringPointsEquiv σ fG g = coveringPointsMap σ fG.hom g := rfl

end Langlands.Geometry.Building
