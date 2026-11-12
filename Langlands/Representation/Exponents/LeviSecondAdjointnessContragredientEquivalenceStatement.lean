import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Contragredient
import Langlands.GroupScheme.Reductive.Basic

/-! # Second adjointness is equivalent to the contragredient formula

Renard 2026, VI.9.6 (printed pp.201–202 / PDF pp.207–208): for a parabolic `P = MN` of `G`
with opposite parabolic `P̄ = M N̄`, second adjointness (VI.9.6.1), `i_P^G ⊣ r_{P̄}^G`, holds
if and only if (VI.9.6.2), `r_{P̄}^G(π̃) ≅ (r_P^G π)~` naturally in `π`, holds. The statement
is pointwise: it is asserted for each fixed pair of parabolics, on carriers in a universe
containing that of the field.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.9.6, equivalence of the two Theorems: for every actual rational parabolic
`P = MN` and every actual rational parabolic `P̄ = M N̄` with the same Levi and
`P(F) ∩ P̄(F) = M(F)`, normalized induction `i_P^G` is left adjoint to normalized Jacquet
restriction `r_{P̄}^G` if and only if the functors `π ↦ r_{P̄}^G(π̃)` and `π ↦ (r_P^G π)~` are
naturally isomorphic, both on carriers in `max u v`. -/
def LeviSecondAdjointnessContragredientEquivalenceStatement : Prop :=
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
        (Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
            leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) ↔
          Nonempty
            (SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
                leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
              (leviJacquetFunctor.{u, max u v} p m n hp hn hm hmul).op ⋙
                SmoothRep.contragredientFunctor.{0, u, max u v}))

end Langlands.Aubert.General.RepresentedParabolic
