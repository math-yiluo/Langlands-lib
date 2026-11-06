import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Contragredient
import Langlands.GroupScheme.Reductive.Basic

/-! # Jacquet modules of contragredients

Renard 2026, VI.9.6 Theorem (VI.9.6.2) (printed p.201/PDF p.207): for a parabolic
`P = MN` of `G` with opposite parabolic `P̄ = M N̄` and every smooth representation `π`
of `G`, `r_{P̄}^G(π̃) ≅ (r_P^G π)~`, naturally in `π`. The opposite parabolic is an
actual rational parabolic with the same Levi whose rational points meet those of `P`
exactly in the Levi image; the contragredient is the published smooth contragredient
functor.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.9.6 Theorem (VI.9.6.2): for every actual rational parabolic `P = MN` and
every actual rational parabolic `P̄ = M N̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`,
the functors `π ↦ r_{P̄}^G(π̃)` and `π ↦ (r_P^G π)~` on smooth representations of `G(F)`
are naturally isomorphic. -/
def LeviJacquetContragredientStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
      (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
        haveI := hm.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
        haveI : LocallyCompactSpace (rationalPoints M) :=
          leviPoints_locallyCompactSpace p m hp hm
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p m hp hm
        Nonempty
          (SmoothRep.contragredientFunctor.{0, u, v} ⋙
              leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
            (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).op ⋙
              SmoothRep.contragredientFunctor.{0, u, v})

end Langlands.Aubert.General.RepresentedParabolic
