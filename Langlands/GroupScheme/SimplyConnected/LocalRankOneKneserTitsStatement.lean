import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Local Kneser–Tits for groups of split rank one

This module states the local Kneser–Tits theorem for almost-simple simply
connected groups of split rank one over a nonarchimedean local field, using
the same normal-subgroup formulation with rational parabolic radicals as
`Langlands.GroupScheme.LocalKneserTitsStatement`. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over any nonarchimedean local field, a normal subgroup of the rational
points of an almost-simple simply connected group of split rank one which
contains the rational unipotent radicals of all rational parabolic subgroups
is the whole group. The radical is the represented geometric unipotent
radical, and the field characteristic and universe are unrestricted. -/
def LocalRankOneKneserTitsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G → IsAlmostSimple G → splitRank G = 1 →
    ∀ (N : Subgroup (rationalPoints G)), N.Normal →
      (∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) (r : U ⟶ P),
        IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p)).range ≤ N) →
      N = ⊤

end Langlands.GroupScheme
