import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Intertwining.PQRegularity
import Langlands.GroupScheme.Reductive.Basic

/-! # Two remarks of Chapter VII (Renard VII.2.6 and VII.3.1)

Statements only.

* `TemperedReducibleNotUnitarizableStatement` (VII.2.6, Remark): without irreducibility the
  Corollary of VII.2.6 can fail, that is, some tempered representation is not unitarizable.
* `BruhatIdentityExtremesStatement` (VII.3.1): the double coset `1̄ = P Q` of the identity is
  the least element for the Bruhat order when `Q = P`, and the greatest when `Q = P̄`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.6, Remark: the Corollary of VII.2.6 ("an irreducible tempered representation
is unitary") can fail without irreducibility. For every nonarchimedean local field `k` there
are a connected reductive group `G` over `k` and a smooth representation `π` of `G(k)` that
is tempered (published `IsNormalizedExponentTempered`, which includes admissibility) and not
unitarizable (no invariant positive definite hermitian form). -/
def TemperedReducibleNotUnitarizableStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k],
    ∃ (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)],
        ∃ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
          IsNormalizedExponentTempered hG π ∧ ¬ IsUnitarizable π.representation

/-- Renard VII.3.1, after the Definition of the Bruhat order: for a parabolic `P` of a
connected reductive group over a nonarchimedean local field, the identity double coset
`1̄ = P(F)` is below every element of `P(F) \ G(F) / P(F)` for the Bruhat order
(`P w P ⊆ closure(P w' P)`), so it is the least element for every total order refining it;
and for a parabolic `Q` with the same Levi `M` as `P = MN` and `P(F) ∩ Q(F) = M(F)` (the
opposite parabolic), every element of `P(F) \ G(F) / Q(F)` is below `1̄ = P(F) Q(F)`, so `1̄`
is the greatest element for every refinement. -/
def BruhatIdentityExtremesStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p →
      (∀ w : parabolicDoubleCosets p p,
        Geometric.BruhatLE (pointImage p) (pointImage p)
          (identityParabolicDoubleCoset p p) w) ∧
      ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (lQ : M ⟶ Q),
        IsParabolicSubgroup q → IsRationalLeviSubgroup l → IsRationalLeviSubgroup lQ →
        lQ ≫ q = l ≫ p →
        pointImage p ⊓ pointImage q = pointImage (l ≫ p) →
        ∀ w : parabolicDoubleCosets p q,
          Geometric.BruhatLE (pointImage p) (pointImage q) w
            (identityParabolicDoubleCoset p q)

end Langlands.Aubert.General.RepresentedParabolic
