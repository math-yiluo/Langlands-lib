import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Dynamic.LieStatement

/-! # Actual standard families inside a represented standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual standard Levi has precisely the selected simple roots, and its
standard subgroup functors are the inverse images of the ambient standard
subgroup functors indexed by subsets of those roots. -/
def StandardLeviStandardFamiliesStatement : Prop :=
  DynamicLieStatement.{u} → StandardCocharacterStatement.{u} →
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
        ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (hL : IsConnectedReductive L)
          (j : L ⟶ G) (hj : (standardLevi i ν J).IsRepresentedBy j),
          IsClosedSubgroup j →
          haveI := hL.isAffineHom
          let iL := standardLeviTorusFactor i ν J hj
          simpleRelativeRoots iL ν = J ∧ IsGenericCocharacter iL ν ∧
            ∀ K : Set (characterLattice T), K ⊆ J →
              standardParabolic iL ν K = (standardParabolic i ν K).comap j ∧
              standardLevi iL ν K = (standardLevi i ν K).comap j ∧
              standardUnipotent iL ν K = (standardUnipotent i ν K).comap j

end Langlands.GroupScheme
