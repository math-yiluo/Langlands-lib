import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Cuspidal embeddings through an actual represented parabolic

Renard VI.2.1, Corollary and proof, printed p.139 / PDF p.145:
an irreducible smooth representation has a nonzero supercuspidal Jacquet
module and embeds into induction from an irreducible supercuspidal quotient
at that same Levi.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.2.1, Corollary and proof, on the actual represented-parabolic
interface, without a standardness or structural-existence premise. -/
def LeviCuspidalEmbeddingStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsIrreducible →
      ∃ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : LocallyCompactSpace (rationalPoints M) :=
          leviPoints_locallyCompactSpace p l hp hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let J := (leviJacquetFunctor.{u, v} p l r hp hr hl hmul).obj π
        Nontrivial J ∧
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' →
            Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj J)) ∧
        ∃ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
          ρ.IsIrreducible ∧
          (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
            (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
            (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
            (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
            (hmul' : IsIso (subgroupMultiplication l' r')),
            ¬ IsIso p' →
              Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) ∧
          (∃ q : J.representation.IntertwiningMap ρ.representation,
            Function.Surjective q) ∧
          ∃ f : π.representation.IntertwiningMap
              ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj ρ).representation,
            Function.Injective f

end Langlands.Aubert.General.RepresentedParabolic
