import Langlands.Representation.Aubert.General.ContragredientJacquetTransport
import Langlands.Representation.Exponents.LeviJacquetContragredientStatement

/-! # Jacquet modules of contragredients on Levi points from the literal Levi image

Renard 2026, VI.9.6 Theorem (VI.9.6.2) (printed p.201, PDF p.207), transport step for
represented parabolics. Let `P = MN` and `P̄ = M N̄` be represented parabolics with
`mbar ≫ pbar = m ≫ p`. A natural isomorphism `r_{N̄}(π~) ≅ (r_N π)~` of normalized Jacquet
functors to smooth representations of the literal Levi image `pointImage (m ≫ p)` gives the
isomorphism of `LeviJacquetContragredientStatement` between the functors to smooth
representations of `M(F)` itself.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance jacquetContragredientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Jacquet modules of contragredients for represented parabolics from the literal Levi
image: if `mbar ≫ pbar = m ≫ p` and the normalized Jacquet functors of the closed subgroups
`N̄(F) = pointImage (nbar ≫ pbar)` and `N(F) = pointImage (n ≫ p)` to smooth representations
of `pointImage (m ≫ p)` satisfy `r_{N̄}(π~) ≅ (r_N π)~` naturally, then
`π ↦ r_{P̄}^G(π~)` and `π ↦ (r_P^G π)~` are naturally isomorphic as functors to smooth
representations of `M(F)`. -/
theorem nonempty_leviJacquetContragredient_iso_of_pointImage
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (hiso : ∀ (hU : IsClosed (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hO : IsClosed (pointImage (n ≫ p) : Set (rationalPoints G)))
      (hMU : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hMO : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (n ≫ p) : Set (rationalPoints G))),
      Nonempty (SmoothRep.contragredientFunctor.{0, u, v} ⋙
          normalizedJacquetFunctor.{u, v} (pointImage (nbar ≫ pbar)) (pointImage (m ≫ p))
            hU hMU ≅
        (normalizedJacquetFunctor.{u, v} (pointImage (n ≫ p)) (pointImage (m ≫ p))
            hO hMO).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v})) :
    letI := leviPointTopology m hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty
      (SmoothRep.contragredientFunctor.{0, u, v} ⋙
          leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v}) := by
  let := leviPointTopology m hm
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p m hp hm
  have hO := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  exact nonempty_contragredient_normalizedJacquet_pullback_iso
    (pointImage (nbar ≫ pbar)) (pointImage (n ≫ p)) (congrArg pointImage hP)
    (isClosed_pointImage_comp pbar nbar hpbar.isClosedSubgroup hnbar.1.isClosedSubgroup) hO
    (pointImage_le_normalizer pbar mbar nbar hnbar) (pointImage_le_normalizer p m n hn)
    (leviPointsEquiv pbar mbar hpbar hmbar) (leviPointsEquiv p m hp hm)
    (fun x => by simp only [leviPointsEquiv_apply_coe, hP])
    (fun hMU => hiso _ hO hMU _)

end Langlands.Aubert.General.RepresentedParabolic
