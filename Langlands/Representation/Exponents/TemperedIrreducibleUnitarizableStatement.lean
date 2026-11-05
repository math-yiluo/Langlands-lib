import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Unitary.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Irreducible tempered representations are unitarizable

Renard 2026, VII.2.6, Corollary (printed p.232/PDF p.238): an irreducible tempered
representation is unitary. Unitarity is the published algebraic predicate
`Langlands.IsUnitarizable`: existence of a positive definite invariant Hermitian form.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.6, Corollary: every irreducible normalized-exponent tempered smooth
representation of `G(F)` admits a positive definite invariant Hermitian form. -/
def TemperedIrreducibleUnitarizableStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsIrreducible → IsNormalizedExponentTempered hG π →
        IsUnitarizable π.representation

end Langlands.Aubert.General.RepresentedParabolic
