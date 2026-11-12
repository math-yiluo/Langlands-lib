import Langlands.Representation.Intertwining.PQRegularity
import Langlands.GroupScheme.Reductive.Basic

/-! # The identity support image for opposite rational parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For opposite represented rational parabolics with the same actual Levi, the identity
support image in `r_Q i_P` is equivariantly isomorphic to the inducing representation. -/
def OppositeIdentitySupportStatement : Prop :=
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
      lQ ≫ q = l ≫ p →
      pointImage p ⊓ pointImage q = pointImage (l ≫ p) →
      ∀ σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M),
        letI := leviPointTopology l hl
        Nonempty
          (((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
            (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.Equiv σ.representation)

end Langlands.Aubert.General.RepresentedParabolic
