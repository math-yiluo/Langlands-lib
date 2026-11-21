import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Reductive.Basic

/-! # Testing unitary Jacquet vanishing on proper standard parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- In the setting of Renard VII.2.4, vanishing of the unitary Jacquet part
for every proper rational parabolic is equivalent to vanishing for the
proper parabolic and Levi pairs in any fixed standard family. -/
def UnitaryJacquetVanishingStandardReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T),
      IsMaximalSplitTorus i → IsGenericCocharacter i ν →
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
          (A : CommGroupScheme (Spec (CommRingCat.of k)))
          (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
          (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
          (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
          (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
          ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥) ↔
        ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
          ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
            SubgroupFunctor.range p = standardParabolic i ν J →
            SubgroupFunctor.range (l ≫ p) = standardLevi i ν J →
            ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥

end Langlands.Aubert.General.RepresentedParabolic
