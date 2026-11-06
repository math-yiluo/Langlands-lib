import Langlands.Representation.Smooth.CompactCompletion
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.GroupScheme.Reductive.Basic

/-! # Second adjointness and completion

Renard 2026, VI.9.7, Theorem (printed p.205/PDF p.211): for a parabolic `P = MN` of `G`
with opposite parabolic `P̄ = M N̄`, and every smooth representation `(π, V)` of `G`,
there is a natural isomorphism `φ : V̄^N ≃ \overline{V_{N̄}}` between the `N`-invariants of
the completion of `V` and the completion of the Jacquet module along `N̄`, characterized
by `e_{K_M} · φ(v) = j_{N̄}(e_K · v)` for every compact open subgroup `K` of `G` admitting
an Iwahori decomposition along `P`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.CompactCompletion
open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

/-- Renard VI.9.7, Theorem: for actual rational parabolics `P = MN` and `P̄ = M N̄` with
the same Levi and `P(F) ∩ P̄(F) = M(F)`, there is a family of linear isomorphisms
`φ_π : V̄^N ≃ \overline{r_{P̄}^G(V)}`, one for every smooth representation `(π, V)` of
`G(F)`, from the `N(F)`-invariants of the completion of `V` to the completion of the
Jacquet module of `V` along `N̄`, such that:

* (characterization) for every compact open subgroup `K` of `G(F)` and every element `g`
  central in `M(F)` satisfying the Iwahori contraction conditions for `(N̄, M, N)`, and
  for the compact open subgroup `K_M` of `M(F)` with underlying set `K ∩ M(F)`, the
  `K_M`-component of `φ_π(v)` is `j_{N̄}(v_K)`, the Jacquet image of the `K`-component of
  `v`;
* (naturality) for every morphism `f : π → σ`, if the components of `w ∈ W̄^N` are the
  images under `f` of the components of `v ∈ V̄^N`, then the components of `φ_σ(w)` are the
  images under `r_{P̄}^G(f)` of the components of `φ_π(v)`. -/
def LeviCompletionOppositeJacquetStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m),
      LeviSubgroup.IsGeometricUnipotentRadical n →
      IsIso (subgroupMultiplication m n) →
      ∀ (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
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
        let rPbar := leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar
        let NG : Subgroup (rationalPoints G) := pointImage (n ≫ p)
        let NbarG : Subgroup (rationalPoints G) := pointImage (nbar ≫ pbar)
        let MG : Subgroup (rationalPoints G) := pointImage (m ≫ p)
        let incM : rationalPoints M → rationalPoints G := fun x =>
          (leviPointsEquiv pbar mbar hpbar hmbar x : rationalPoints G)
        ∃ φ : ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
            completionFixed π.representation π.isSmooth NG ≃ₗ[ℂ]
              completion (rPbar.obj π).representation (rPbar.obj π).isSmooth,
          (∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
              (x : completionFixed π.representation π.isSmooth NG)
              (K : CompactOpenSubgroup (rationalPoints G)) (g : rationalPoints G),
              (∀ y ∈ MG, y * g = g * y) →
              Jacquet.IsIwahoriContraction K.1 NbarG MG NG g →
              ∀ KM : CompactOpenSubgroup (rationalPoints M), (∀ y, y ∈ KM.1 ↔ incM y ∈ K.1) →
                ((φ π x : completion (rPbar.obj π).representation (rPbar.obj π).isSmooth) :
                    CompactOpenSubgroup (rationalPoints M) → rPbar.obj π) KM =
                  Jacquet.Localization.mk π.representation NbarG 1
                    (((x : completion π.representation π.isSmooth) :
                      CompactOpenSubgroup (rationalPoints G) → π) K)) ∧
          ∀ (π σ : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (f : π ⟶ σ)
            (x : completionFixed π.representation π.isSmooth NG)
            (y : completionFixed σ.representation σ.isSmooth NG),
            (∀ K : CompactOpenSubgroup (rationalPoints G),
              ((y : completion σ.representation σ.isSmooth) :
                  CompactOpenSubgroup (rationalPoints G) → σ) K =
                SmoothRep.hom f (((x : completion π.representation π.isSmooth) :
                  CompactOpenSubgroup (rationalPoints G) → π) K)) →
            ∀ KM : CompactOpenSubgroup (rationalPoints M),
              ((φ σ y : completion (rPbar.obj σ).representation (rPbar.obj σ).isSmooth) :
                  CompactOpenSubgroup (rationalPoints M) → rPbar.obj σ) KM =
                SmoothRep.hom (rPbar.map f)
                  (((φ π x : completion (rPbar.obj π).representation
                      (rPbar.obj π).isSmooth) :
                    CompactOpenSubgroup (rationalPoints M) → rPbar.obj π) KM)

end Langlands.Aubert.General.RepresentedParabolic
