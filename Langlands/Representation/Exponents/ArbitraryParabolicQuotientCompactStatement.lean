import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Group.LeftQuotient
import Langlands.GroupScheme.Reductive.Basic

/-! # Compactness target for every represented parabolic quotient

Renard 2026, V.5.1 Corollary (printed p.123 / PDF p.129), expressed on
the literal rational-point image and the existing quotient topology.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Compactness of the actual rational-point quotient for every represented
parabolic, in the ambient scope of the arbitrary-parabolic exponent theorem. -/
def ArbitraryParabolicQuotientCompactStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (_hp : IsParabolicSubgroup p),
      CompactSpace (Induction.LeftQuotient (pointImage p))

end Langlands.Aubert.General.RepresentedParabolic
