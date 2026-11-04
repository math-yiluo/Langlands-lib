import Langlands.GroupScheme.Rational.ParabolicRootPresentation

/-! # Statements: existence and independence of parabolic root presentations

These structural targets quantify over specified actual parabolic, rational
Levi and split-component maps. Independence allows every field of the root
presentation to vary.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Every specified rational parabolic, rational Levi and Levi split component
of a connected reductive group admits a compatible root presentation. -/
def ParabolicRootPresentationExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (P M : GroupScheme (Spec (CommRingCat.of k)))
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M),
    haveI := hG.isAffineHom
    IsParabolicSubgroup p → IsRationalLeviSubgroup l → IsSplitComponent a →
      Nonempty (ParabolicRootPresentation p l a)

/-- For the same specified maps, any two compatible presentations have the
same restricted simple-root set and the same two root-combination cones.
Their maximal split tori, generic cocharacters and simple-root indices may
all differ. -/
def ParabolicRootPresentationIndependenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (P M : GroupScheme (Spec (CommRingCat.of k)))
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    ∀ r s : ParabolicRootPresentation p l a,
      r.restrictedRoots = s.restrictedRoots ∧
      r.positiveCone = s.positiveCone ∧
      r.nonnegCone = s.nonnegCone

/-- A compatible isomorphism between specified split-component presentations
identifies the restricted roots and both cones by real character pullback
in both directions, even when every root-presentation choice differs. -/
def ParabolicRootPresentationIsoStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (P M : GroupScheme (Spec (CommRingCat.of k)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (a' : A'.toGrp ⟶ M)
    (e : A ≅ A'),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    CommGroupScheme.groupHom e.hom ≫ a' = a →
    ∀ (r : ParabolicRootPresentation p l a)
      (s : ParabolicRootPresentation p l a'),
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        s.restrictedRoots = r.restrictedRoots ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        r.restrictedRoots = s.restrictedRoots ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        s.positiveCone = r.positiveCone ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        r.positiveCone = s.positiveCone ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        s.nonnegCone = r.nonnegCone ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        r.nonnegCone = s.nonnegCone

/-- The exact existence, full choice-independence and compatible-component
transport obligations for Renard V.3.14–V.3.15. -/
def ParabolicRootPresentationStatement : Prop :=
  ParabolicRootPresentationExistenceStatement.{u} ∧
  ParabolicRootPresentationIndependenceStatement.{u} ∧
  ParabolicRootPresentationIsoStatement.{u}

end Langlands.GroupScheme
