import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement

/-! # Dominant Weyl displacement in the real character space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Renard (VII.4.1.3). The difference between a dominant real character
and its inverse Weyl translate is a nonnegative sum of simple roots. -/
def DominantWeylDisplacementStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ (D : RelativeRootReflectionData i) (x : Vstar T),
      (∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
        0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) →
      ∀ w : relativeWeylGroup i,
        x - relativeWeylFullRealAction i w⁻¹ x ∈
          PointedCone.hull ℝ
            ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' simpleRelativeRoots i ν)

end Langlands.GroupScheme
