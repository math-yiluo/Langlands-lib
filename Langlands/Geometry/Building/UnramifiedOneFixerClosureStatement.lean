import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # One-group fixers over the maximal unramified extension do not see closures -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedOneFixerClosureAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The real affine topology on the apartment of supplied building data over the
maximal unramified extension: the initial topology of all real affine functionals.
It is specified without choosing a norm or an origin. -/
@[instance_reducible] def unramifiedApartmentTopology {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)) :
    TopologicalSpace C.Apartment :=
  ⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance

/-- The elementary inclusion: a subset lies in its closure, so every element fixing the
translated closure pointwise fixes the translated subset pointwise. -/
theorem characterValuationKernel_inf_pointwiseFixer_closure_le
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (Ωa : Set C.Apartment) :
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      C.pointwiseFixer ((fun x => g • C.apartmentMap x) ''
        @closure C.Apartment (unramifiedApartmentTopology C) Ωa) ≤
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) :=
  inf_le_inf_left _ (fun h hh => by
    rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer] at hh ⊢
    rintro _ ⟨x, hx, rfl⟩
    exact hh _ ⟨x, (@subset_closure C.Apartment (unramifiedApartmentTopology C) Ωa) hx, rfl⟩)

/-- **The groups `G(K)^1_Ω` do not change under closure** (Kaletha–Prasad Lemma 7.4.4(3),
§7.7 and Proposition 7.7.5(1) for `∗ = 1`, over the maximal unramified extension `K` of a
nonarchimedean local field `F`). Let `C` be supplied building data of `G_K`. For every
nonempty bounded subset `Ωa` of the apartment of `C` and every `g ∈ G(K)`, the pointwise
fixer in `G(K)^1` of the translate `g · Ωa` in the reduced building equals the pointwise
fixer in `G(K)^1` of the translate `g · cl(Ωa)` of its closure for the real affine
topology. Here `G(K)^1` is the kernel of the valuations of all rational characters of
`G_K`. -/
def UnramifiedOneFixerClosureStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Ωa : Set C.Apartment),
    Ωa.Nonempty → (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) →
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) =
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      C.pointwiseFixer ((fun x => g • C.apartmentMap x) ''
        @closure C.Apartment (unramifiedApartmentTopology C) Ωa)

end Langlands.Geometry.Building
