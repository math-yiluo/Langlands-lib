import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Zero-group fixers over the maximal unramified extension depend only on affine-root signs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedZeroFixerAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **The parahoric subgroup `G(K)^0_Ω` depends only on the affine roots nonnegative on `Ω`**
(derived from Kaletha–Prasad Definition 7.4.1, Lemma 7.4.4(3), Proposition 7.7.5(1) and
Lemma 2.6.24, over the maximal unramified extension `K` of a nonarchimedean local field `F`).
Let `C` be supplied building data of `G_K` and `E` any datum computing `G(K)^0` as
`E.zeroPoints`. Let `Ωa`, `Ωa'` be nonempty subsets of the apartment of `C` on which every real
affine function is bounded above, and assume that every affine root `ψ ∈ C.affineRoots` is
nonnegative on all of `Ωa` if and only if it is nonnegative on all of `Ωa'`. Then for every
`g ∈ G(K)` the pointwise fixers in `G(K)^0` of the translates `g · Ωa` and `g · Ωa'` in the
reduced building of `C` agree. -/
def UnramifiedZeroFixerAffineRootStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Ωa Ωa' : Set C.Apartment),
    Ωa.Nonempty → (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) →
    Ωa'.Nonempty → (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa')) →
    (∀ ψ ∈ C.affineRoots, (∀ x ∈ Ωa, 0 ≤ ψ x) ↔ (∀ x ∈ Ωa', 0 ≤ ψ x)) →
    E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa')

end Langlands.Geometry.Building
