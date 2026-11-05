import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Rational.AffineLineRigidity
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.SeparableClosure

/-! # Vector factors of smooth connected commutative p-torsion groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The existence assertion of CGP B.2.5: a smooth connected commutative
p-torsion affine group is a product of a vector group and a complement
whose affine-line maps are constant over the separable closure. -/
def CommutativePTorsionVectorFactorStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : CommGroupScheme (Spec (CommRingCat.of k))),
    Smooth U.X.hom → IsAffineHom U.X.hom → ConnectedSpace U.X.left →
    HasUniformPowerExponent U.toGrp p →
      ∃ (V : GroupScheme (Spec (CommRingCat.of k)))
        (W : CommGroupScheme (Spec (CommRingCat.of k))),
        Nonempty (U.toGrp ≅ V ⊗ W.toGrp) ∧ IsVectorGroup V ∧
        Smooth W.X.hom ∧ IsAffineHom W.X.hom ∧ ConnectedSpace W.X.left ∧
        IsUnipotent W.toGrp ∧
        HasConstantAffineLineMaps
          ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj W.toGrp)

end Langlands.GroupScheme.RelativeRoot
