import Langlands.Representation.Geometric.RepresentedParabolicSupportOrbit
import Langlands.Representation.Geometric.RepresentedParabolicCoinvariants

/-! # The local normalized orbit comparison for represented parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The local normalized calculation: compact stabilizer induction followed by
normalized target-radical coinvariants is the actual intersection piece. -/
def RepresentedGeometricLemmaOrbitComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q L U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ))
      (z : rationalPoints G)
      (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ z),
      letI := leviPointTopology l hl
      Nonempty (smoothLeviInducingFunctor.{u, v} p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ ⋙
          leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ ≅ D.pieceFunctor)

end Langlands.Aubert.General.RepresentedParabolic
