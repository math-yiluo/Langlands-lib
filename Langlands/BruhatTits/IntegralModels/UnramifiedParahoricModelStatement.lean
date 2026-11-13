import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Parahoric models over the maximal unramified integers (KP 8.3.2 and 8.3.13) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

private instance unramifiedParahoricModelAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- At one point the full-model subgroup of the statement below is the published
one-group stabilizer `K_y = G(K)^1 ∩ G(K)_y`. -/
theorem characterValuationKernel_inf_pointwiseFixer_singleton
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (y : C.ReducedBuilding) :
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ C.pointwiseFixer {y} =
      C.oneStabilizer y := by
  rw [IntegerValuationBuildingData.pointwiseFixer,
    KPApartmentData.pointwiseFixer_singleton]

/-- **KP Theorems 8.3.2 and 8.3.13 over the maximal unramified extension.**
Let `G` be an affine group over a nonarchimedean local field `F`, let `K` be the
maximal unramified extension `inertiaFixedField F` with integers
`fixedFieldIntegers F`, and let `C` be supplied building data of `G_K` for the
normalized valuation of `K`. For every nonempty bounded subset `Ω` of a
translated apartment `g · A(S)` of `C` there is a smooth affine model of `G_K`
over the integers of `K` with integral points `G(K)^1_Ω = G(K)^1 ∩ G(K)_Ω`,
together with its relative identity component, a smooth affine model with
connected fibres and integral points `G(K)^0_Ω = G(K)^0 ∩ G(K)_Ω`. Here
`G(K)^1` is the kernel of the valuations of all rational characters of `G_K`,
`G(K)^0` is the subgroup of KP Definition 2.6.23(1) computed from any supplied
datum `E`, and `G(K)_Ω` is the pointwise fixer of `Ω` in the reduced building
of `C`. -/
def UnramifiedParahoricModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Ωa : Set C.Apartment),
    Ωa.Nonempty →
    (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) →
    ∃ D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
        (baseChanged F (inertiaFixedField F) G),
      D.full.integralPoints =
          characterValuationKernel (MaximalUnramified.valuation F)
              (baseChanged F (inertiaFixedField F) G) ⊓
            C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) ∧
      D.neutral.integralPoints =
          E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa)

end Langlands.BruhatTits.IntegralModels
