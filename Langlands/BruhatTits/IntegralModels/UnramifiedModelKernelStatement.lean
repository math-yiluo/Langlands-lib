import Langlands.BruhatTits.IntegralModels.ModelMorphism
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # The kernel of the special-fibre map between unramified parahoric models (KP 8.4.15) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

private instance unramifiedModelKernelAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **KP Proposition 8.4.15 over the maximal unramified integers.**
Let `G` be an affine group over a nonarchimedean local field `F`, let `K` be the
maximal unramified extension `inertiaFixedField F` with integers
`fixedFieldIntegers F`, let `C` be supplied building data of `G_K` for the
normalized valuation of `K` (it records that `G_K` is connected reductive), and
let `E` be a datum computing `G(K)^0`. Let `Ωa` and `Ωa'` be subsets of the
apartment of `C`, with `Ωa` nonempty, `Ωa'` bounded, and `Ωa` contained in the
closure of `Ωa'` for the topology of real affine functionals, both translated
by the same `g ∈ G(K)`. For smooth models `N`, `N'` of `G_K` over the integers
of `K` with integral points `G(K)^0 ∩ G(K)_{g Ωa}` and `G(K)^0 ∩ G(K)_{g Ωa'}`,
every model homomorphism `N' → N` with identity generic fibre has a smooth,
connected and unipotent scheme-theoretic kernel on special fibres. -/
def UnramifiedModelKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Ωa Ωa' : Set C.Apartment),
    Ωa.Nonempty →
    (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa')) →
    Ωa ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ωa' →
    ∀ (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
        (baseChanged F (inertiaFixedField F) G)),
      N.IsSmooth → N'.IsSmooth →
      N.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) →
      N'.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa') →
      ∀ ψ : N'.Hom N (𝟙 _),
        Smooth (kernel ψ.specialFibreMap).X.hom ∧
          ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
            IsUnipotent (kernel ψ.specialFibreMap)

end Langlands.BruhatTits.IntegralModels
