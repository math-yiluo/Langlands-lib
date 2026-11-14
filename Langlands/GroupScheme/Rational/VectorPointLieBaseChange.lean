import Langlands.GroupScheme.Rational.VectorCoordinatesBaseChange
import Langlands.GroupScheme.Rational.VectorPointLieEquiv

/-! # The actual vector point-to-Lie comparison under field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsNaturalVectorCoordinates e)
    (K : Type u) [Field K] [Algebra k K]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd V.X.hom (algebraBaseMap k K))
  infer_instance

/-- The epsilon coefficients of actual tangent vectors agree under the
scheme-pullback comparison and the transported vector coordinates. -/
theorem vectorLieCoordinates_baseChange
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (X : Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj V) A)) :
    vectorLieCoordinates (vectorBaseChangeCoordinates e K) he.baseChange
        (CommAlgCat.of K A) X =
      vectorLieCoordinates e he (CommAlgCat.of k A)
        (Lie.kernelBaseChangeLinearEquiv k K V A X) := by
  funext j
  change ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K)
    (DualNumber A) X.toMul.val).toAdd j).snd = _
  rw [vectorAffineCoordinates_baseChange he]
  rfl

/-- The point-to-tangent comparison commutes with actual scheme base change
on every coefficient algebra, including nonreduced algebras. -/
theorem vectorPointLieEquiv_baseChange
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (v : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj V) A) :
    Lie.kernelBaseChangeLinearEquiv k K V A
        (vectorPointLieEquiv (vectorBaseChangeCoordinates e K) he.baseChange
          (CommAlgCat.of K A) (Additive.ofMul v)) =
      vectorPointLieEquiv e he (CommAlgCat.of k A)
        (Additive.ofMul (Lie.affineBaseChangeEquiv k K V A v)) := by
  apply (vectorLieCoordinates e he (CommAlgCat.of k A)).injective
  rw [← vectorLieCoordinates_baseChange e he K A,
    vectorLieCoordinates_vectorPointLieEquiv,
    vectorLieCoordinates_vectorPointLieEquiv]
  exact congrArg Multiplicative.toAdd (vectorAffineCoordinates_baseChange he v)

/-- Transport the original point-to-Lie equivalence through the actual
point and tangent pullback comparisons. -/
def vectorPointLieBaseChangeEquiv
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    Additive (Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj V) A) ≃+
      Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj V) A) :=
  (((Lie.affineBaseChangeEquiv k K V A).toAdditive).trans
    (vectorPointLieEquiv e he (CommAlgCat.of k A))).trans
      (Lie.kernelBaseChangeLinearEquiv k K V A).symm.toAddEquiv

/-- The transported equivalence is precisely the equivalence constructed
from the base-changed natural coordinates. -/
theorem vectorPointLieBaseChangeEquiv_eq
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    vectorPointLieBaseChangeEquiv e he K A =
      vectorPointLieEquiv (vectorBaseChangeCoordinates e K) he.baseChange
        (CommAlgCat.of K A) := by
  apply AddEquiv.ext
  intro v
  apply (Lie.kernelBaseChangeLinearEquiv k K V A).injective
  change (Lie.kernelBaseChangeLinearEquiv k K V A)
    ((Lie.kernelBaseChangeLinearEquiv k K V A).symm
      (vectorPointLieEquiv e he (CommAlgCat.of k A)
        (Additive.ofMul (Lie.affineBaseChangeEquiv k K V A v.toMul)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (vectorPointLieEquiv_baseChange e he K A v.toMul).symm

end Langlands.GroupScheme.RelativeRoot
