import Langlands.Representation.Exponents.LeviJacquetCompletionNormalization
import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.Representation.Smooth.CompactCompletionFixed

/-! # The opposite Jacquet completion formula at all Iwahori indices -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.CompactCompletion
open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

/-- The opposite Jacquet quotient formula on the contraction indices determines
the components at every compact open subgroup with an Iwahori factorization. -/
def LeviCompletionIwahoriFormulaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup m →
      LeviSubgroup.IsGeometricUnipotentRadical n →
      ∀ (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
        (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
        (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
        haveI := hmbar.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology mbar hmbar
        haveI := leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
        let r := leviUnnormalizedJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar
        let NG := pointImage (n ≫ p)
        let NbarG := pointImage (nbar ≫ pbar)
        let MG := pointImage (mbar ≫ pbar)
        let incM := fun z : rationalPoints M =>
          (leviPointsEquiv pbar mbar hpbar hmbar z : rationalPoints G)
        ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
          (x : completionFixed π.representation π.isSmooth NG)
          (y : completion (r.obj π).representation (r.obj π).isSmooth),
          (∀ (L : CompactOpenSubgroup (rationalPoints G)) (g : rationalPoints G),
            (∀ z ∈ MG, z * g = g * z) →
            Jacquet.IsIwahoriContraction L.1 NbarG MG NG g →
            ∀ LM : CompactOpenSubgroup (rationalPoints M),
              (∀ z, z ∈ LM.1 ↔ incM z ∈ L.1) →
              y.1 LM = Jacquet.Localization.mk π.representation NbarG 1 (x.1.1 L)) →
          ∀ (K : CompactOpenSubgroup (rationalPoints G)),
            (∀ a ∈ K.1, ∃ b ∈ K.1.toSubgroup ⊓ NbarG,
              ∃ z ∈ K.1.toSubgroup ⊓ MG, ∃ c ∈ K.1.toSubgroup ⊓ NG, a = b * z * c) →
            ∀ KM : CompactOpenSubgroup (rationalPoints M),
              (∀ z, z ∈ KM.1 ↔ incM z ∈ K.1) →
              y.1 KM = Jacquet.Localization.mk π.representation NbarG 1 (x.1.1 K)

end Langlands.Aubert.General.RepresentedParabolic
