import Langlands.Representation.Exponents.LeviInductionDualityAdjunction
import Langlands.Representation.Category.SecondAdjointnessContragredient
import Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceStatement

/-!
# The represented-Levi contragredient formula from second adjointness

The forward implication of Renard 2026, VI.9.6, for the actual normalized
parabolic induction and Jacquet functors.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviForwardPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The natural Jacquet–contragredient isomorphism constructed from second
adjointness for actual represented parabolics with a common Levi. -/
def leviContragredientIsoOfSecondAdjunction (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar)) :
    let := leviPointTopology m hm
    haveI : LocallyCompactSpace (rationalPoints M) :=
      leviPoints_locallyCompactSpace p m hp hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
        leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) →
      (SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
          leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, max u v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, max u v}) := by
  let := leviPointTopology m hm
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p m hp hm
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p m hp hm
  let C := Classical.choice
    (nonempty_leviInductionContragredientIso.{u, v} hG p m n hp hm hn hmul)
  exact SmoothRep.contragredientIsoOfSecondAdjunction
    (leviFirstAdjointnessAdjunction p m n hp hm hn hmul) C

/-- For actual represented parabolics with a common Levi, second adjointness
implies the natural Jacquet–contragredient isomorphism. -/
theorem nonempty_leviContragredientIso_of_secondAdjunction (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar)) :
    let := leviPointTopology m hm
    haveI : LocallyCompactSpace (rationalPoints M) :=
      leviPoints_locallyCompactSpace p m hp hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
        leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) →
      Nonempty (SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
          leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, max u v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, max u v}) := by
  let := leviPointTopology m hm
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p m hp hm
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p m hp hm
  exact Nonempty.map (leviContragredientIsoOfSecondAdjunction hG p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar)

end Langlands.Aubert.General.RepresentedParabolic
