import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # Standard cocharacters and choice-free standard subgroups -/

/-- Existence of standard cocharacters and agreement of each standard subgroup functor with every standard cocharacter’s dynamic subgroup. -/
def StandardCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        (∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta) ∧
        ∀ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta →
          standardParabolic i ν J = Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ∧
          standardLevi i ν J = Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ∧
          standardUnipotent i ν J = Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)

end Langlands.GroupScheme
