import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Jacquet modules of supercuspidal inductions along non-conjugate Levis

Renard 2026, VI.5.3, Proposition (ii) (printed p.173/PDF p.179): let `P = MN` and
`Q = LU` be parabolic subgroups of `G` and `ρ` a supercuspidal representation of `M`. If
`M` is not conjugate to `L` in `G`, then `r_Q^G i_P^G ρ` has no supercuspidal irreducible
subquotient.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.3, Proposition (ii): for actual rational parabolics `P = MN` and `Q = LU`
and a supercuspidal smooth representation `ρ` of `M(F)`, if `M` is not conjugate to `L`
under `G(F)`, then every irreducible subquotient of `r_Q^G i_P^G ρ` has a nonzero
normalized Jacquet module for some proper actual rational parabolic of `L`. -/
def LeviJacquetInductionNoSupercuspidalStatement : Prop :=
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
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      (¬ ∃ (g : rationalPoints G) (φ : M ≅ L),
          φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      haveI := hlQ.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
      haveI : LocallyCompactSpace (rationalPoints L) :=
        leviPoints_locallyCompactSpace q lQ hq hlQ
      haveI : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q lQ hq hlQ
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints L),
          σ.IsIrreducible →
          SmoothRep.IsSubquotient σ
            ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
              ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) →
          ¬ (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
              (p' : P' ⟶ L) (l' : M' ⟶ P') (r' : U' ⟶ P')
              (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
              (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
              (hmul' : IsIso (subgroupMultiplication l' r')),
              ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj σ))

end Langlands.Aubert.General.RepresentedParabolic
