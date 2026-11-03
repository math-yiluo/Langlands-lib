import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.IdentityComponent

/-! # Connected reductivity of full-kernel centralizer identity components -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

/-- In a connected reductive group, the identity component of the actual
centralizer of the full kernel of a nonzero split-torus character is connected
reductive. The kernel itself need not be smooth. -/
def KernelCentralizerComponentReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (i : S.toGrp ⟶ G) (a : characterLattice S), a ≠ 0 →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
      (kernelCentralizer i a).IsRepresentedBy j →
      ∀ (hclosed : IsClosedSubgroup j) (hC : Smooth C.X.hom),
        letI : Smooth C.X.hom := hC
        letI : IsAffineHom G.X.hom := hG.isAffineHom
        letI : IsClosedImmersion j.hom.hom.left := hclosed
        letI : IsAffineHom C.X.hom := by
          have h : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
          simpa only [Over.w] using h
        IsConnectedReductive (identityComponent C)

end Langlands.GroupScheme.RelativeRoot
