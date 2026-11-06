import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.GroupScheme.Reductive.Basic

/-! # No supercuspidal subquotients in proper parabolic induction

Renard 2026, VI.5.2, Lemma (printed p.173/PDF p.179): let `P = MN` be a proper parabolic
subgroup of `G` and `ρ` a smooth representation of `M`. Then no irreducible subquotient of
`i_P^G ρ` is supercuspidal. Supercuspidality is the vanishing of the normalized Jacquet
module for every proper actual parabolic.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.2, Lemma: for every proper actual rational parabolic `P = MN` and every
smooth representation `ρ` of `M(F)`, every irreducible subquotient `σ` of `i_P^G ρ` has a
nonzero normalized Jacquet module for some proper actual rational parabolic of `G`. -/
def LeviInductionNoSupercuspidalSubquotientStatement : Prop :=
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
      (hmul : IsIso (subgroupMultiplication l r)),
      ¬ IsIso p →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
        (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
        σ.IsIrreducible →
        SmoothRep.IsSubquotient σ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
        ¬ (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
            (p' : P' ⟶ G) (l' : M' ⟶ P') (r' : U' ⟶ P')
            (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
            (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
            (hmul' : IsIso (subgroupMultiplication l' r')),
            ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj σ))

end Langlands.Aubert.General.RepresentedParabolic
