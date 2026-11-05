import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.GroupScheme.Reductive.Basic

/-! # Admissibility of the actual normalized Jacquet module

Renard 2026, VI.6.1 Corollary (printed pp.176–177 / PDF pp.182–183),
normalized clause, for every represented parabolic.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.6.1 Corollary: the actual normalized Jacquet functor of every
represented parabolic preserves admissibility. This is a proposition target. -/
def ArbitraryParabolicJacquetAdmissibilityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsAdmissible →
        ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible

end Langlands.Aubert.General.RepresentedParabolic
