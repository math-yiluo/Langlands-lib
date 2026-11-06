import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.GroupScheme.Reductive.Basic

/-! # Realization of an admissible supercuspidal subquotient

Renard 2026, VI.3.6, Lemma (printed pp.147–148 / PDF pp.153–154):
an irreducible supercuspidal subquotient of an admissible smooth representation
occurs as both a subrepresentation and a quotient.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.3.6, Lemma, for all actual connected reductive groups and all
proper actual rational parabolics: an irreducible supercuspidal actual smooth
subquotient of an admissible representation embeds into it and is its quotient.
The two maps need not split one another. -/
def RepresentedSupercuspidalSubquotientRealizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsAdmissible →
      τ.IsIrreducible →
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj τ)) →
      SmoothRep.IsSubquotient τ π →
      SmoothRep.IsSubrepresentation τ π ∧ SmoothRep.IsQuotient τ π

end Langlands.Aubert.General.RepresentedParabolic
