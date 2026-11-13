import Langlands.GroupScheme.Rational.SplitComponentCocharacters
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Integral simple-root annihilators and actual split components -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The common integral annihilator of the actual simple relative roots is
exactly the cocharacter image of the actual split component, along any compatible
factorization through the chosen maximal split torus. -/
def SimpleRootSplitCentralImageStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
        IsSplitComponent a → ∀ (f : A ⟶ T),
          CommGroupScheme.groupHom f ≫ i = a →
            RealTorusSpace.rootAnnihilatorInt T (simpleRelativeRoots i ν) =
              (RealTorusSpace.cocharacterMapInt f).range

end Langlands.GroupScheme
