import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Jacquet modules of supercuspidal inductions vanish without conjugate Levis

Renard 2026, VI.5.3, Proposition (i) (printed p.173/PDF p.179): let `P = MN` and
`Q = LU` be parabolic subgroups of `G` and `ρ` a supercuspidal representation of `M`. If
`L` has no Levi subgroup conjugate to `M` in `G`, then `r_Q^G i_P^G ρ = 0`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.3, Proposition (i): for actual rational parabolics `P = MN` and `Q = LU`
and a supercuspidal smooth representation `ρ` of `M(F)` (every normalized Jacquet module of
`ρ` for a proper actual parabolic of `M` vanishes), if no Levi subgroup of an actual
rational parabolic of `L` is conjugate to `M` under `G(F)`, then the normalized Jacquet
module of `i_P^G ρ` along `Q` vanishes. -/
def LeviJacquetInductionVanishingStatement : Prop :=
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
      (¬ ∃ (P'' M'' : GroupScheme (Spec (CommRingCat.of k)))
          (p'' : P'' ⟶ L) (l'' : M'' ⟶ P''),
          IsParabolicSubgroup p'' ∧ IsRationalLeviSubgroup l'' ∧
          ∃ (g : rationalPoints G) (φ : M ≅ M''),
            φ.hom ≫ l'' ≫ p'' ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        Subsingleton
          ((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
            ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))

end Langlands.Aubert.General.RepresentedParabolic
