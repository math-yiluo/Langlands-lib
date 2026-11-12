import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Plancherel.RationalImageCharacters

/-! # Strict displacement of the split component on non-identity same-Levi pieces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For represented parabolics `P = MN` and `Q = MU` with the same Levi subgroup, a split
component `a : A → M`, a representative `z` of a double coset `P(F) z Q(F)` different from
`P(F) Q(F)`, intersection data at `z`, and any factorization `b` of `a` through the Levi
`L' = M ∩ z⁻¹ M z` of the second intersection parabolic: some `t ∈ A(F)` has
`a(t)` and the conjugate `z a(t) z⁻¹ = (b ≫ φ ≫ l' ≫ p')(t)` with different images under
the valuation map `M(F) → Hom(X^*(M)_F, ℤ)`. -/
def SameLeviPieceStrictDisplacementStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        ∀ z : rationalPoints G,
          DoubleCoset.mk (pointImage p) (pointImage q) z ≠ identityParabolicDoubleCoset p q →
          ∀ (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
            (b : A.toGrp ⟶ D.L'), b ≫ D.lQ' ≫ D.q' = a →
            ∃ t : rationalPoints A.toGrp,
              Plancherel.rationalValuationImageProjection M (rationalPoints.map a t) ≠
                Plancherel.rationalValuationImageProjection M
                  (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p') t)

end Langlands.Aubert.General.RepresentedParabolic
