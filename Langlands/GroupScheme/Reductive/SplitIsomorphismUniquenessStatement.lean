import Langlands.GroupScheme.Adjoint.SplitTorus
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Unpinned uniqueness in the split Isomorphism Theorem -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two isomorphisms of split reductive groups with the same pullback on the
actual characters of their supplied maximal tori differ by the inner action
of a unique ground-field point of the target torus modulo the full centre.
The quotient torus is supplied as an actual fppf image in an adjoint quotient. -/
def SplitIsomorphismUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G G' A : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T T' T'_ad : CommGroupScheme (Spec (CommRingCat.of k))),
      IsSplitTorus T.toGrp →
      ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G')
        (q : G' ⟶ A) (j : T'_ad.toGrp ⟶ A) (π : T' ⟶ T'_ad)
        (h : IsAdjointSplitTorusImage q i' j π),
        IsMaximalTorus i → IsMaximalTorus i' →
        ∀ (φ₁ φ₂ : G ≅ G') (t₁ t₂ : T ≅ T'),
          i ≫ φ₁.hom = CommGroupScheme.groupHom t₁.hom ≫ i' →
          i ≫ φ₂.hom = CommGroupScheme.groupHom t₂.hom ≫ i' →
          (∀ χ : characterLattice T', t₁.hom ≫ χ = t₂.hom ≫ χ) →
          ∃! x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T'_ad.toGrp.X,
            φ₁ ≪≫ h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom) = φ₂

end Langlands.GroupScheme
