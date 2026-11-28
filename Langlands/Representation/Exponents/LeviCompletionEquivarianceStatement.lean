import Langlands.Representation.Exponents.LeviCompletionOppositeJacquetStatement
import Langlands.Representation.Exponents.LeviJacquetCompletionNormalization
import Langlands.Representation.Smooth.CompactCompletionAction
import Langlands.Representation.Smooth.CompactCompletionMaps

/-! # Equivariance of the opposite Jacquet completion comparison -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.CompactCompletion
open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

/-- The comparison of VI.9.7, transported to the unnormalized Jacquet
completion, is uniquely characterized by its component formula. It
intertwines Levi translation on the radical-fixed completion with Levi
translation on the unnormalized Jacquet completion, and commutes with the
componentwise completion maps of intertwiners. -/
def LeviCompletionEquivarianceStatement : Prop :=
  LeviCompletionOppositeJacquetStatement.{u, v} →
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
      IsIso (subgroupMultiplication m n) →
      ∀ (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
        (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
        (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar),
      IsIso (subgroupMultiplication mbar nbar) →
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
        haveI := hmbar.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology mbar hmbar
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup pbar mbar hpbar hmbar
        let r := leviUnnormalizedJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar
        let NG := pointImage (n ≫ p)
        let NbarG := pointImage (nbar ≫ pbar)
        let MG := pointImage (mbar ≫ pbar)
        let incM := fun z : rationalPoints M =>
          (leviPointsEquiv pbar mbar hpbar hmbar z : rationalPoints G)
        let Source := fun π : SmoothRep.{0, u, v} ℂ (rationalPoints G) =>
          completionFixed π.representation π.isSmooth NG
        let Target := fun π : SmoothRep.{0, u, v} ℂ (rationalPoints G) =>
          completion (r.obj π).representation (r.obj π).isSmooth
        let HasComponentFormula := fun φ : ∀ π, Source π ≃ₗ[ℂ] Target π =>
          ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (x : Source π)
            (K : CompactOpenSubgroup (rationalPoints G)) (g : rationalPoints G),
            (∀ y ∈ MG, y * g = g * y) →
            Jacquet.IsIwahoriContraction K.1 NbarG MG NG g →
            ∀ KM : CompactOpenSubgroup (rationalPoints M),
              (∀ z, z ∈ KM.1 ↔ incM z ∈ K.1) →
              (φ π x).1 KM = Jacquet.Localization.mk π.representation NbarG 1 (x.1.1 K)
        ∃ φ : ∀ π, Source π ≃ₗ[ℂ] Target π,
          HasComponentFormula φ ∧
          (∀ ψ, HasComponentFormula ψ → ψ = φ) ∧
          (∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (z : rationalPoints M)
              (x : Source π),
            ∃ y : Source π, y.1.1 = translate π.representation (incM z) x.1.1 ∧
              φ π y =
                action (r.obj π).representation (r.obj π).isSmooth z (φ π x)) ∧
          ∀ (π σ : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (f : π ⟶ σ) (x : Source π),
            φ σ (mapFixed π.isSmooth σ.isSmooth NG (SmoothRep.hom f) x) =
              map (r.obj π).isSmooth (r.obj σ).isSmooth (SmoothRep.hom (r.map f)) (φ π x)

end Langlands.Aubert.General.RepresentedParabolic
