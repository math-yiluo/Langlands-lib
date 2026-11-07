import Langlands.Geometry.Building.IntegerCentralizerFieldRestriction
import Langlands.Geometry.Building.MaximalUnramifiedRootRestriction

/-! # Actual local centralizer compatibility from unramified restriction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable Langlands.BruhatTits
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

local notation "b" => algebraBaseMap F (inertiaFixedField F)
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "s_K" s => CategoryTheory.Functor.map (GroupScheme.baseChange b) s

/-- Actual positive centralizer valuations agree on original points with the
existing local-field valuation, through actual split cocharacter base change. -/
theorem centralizerValuation_base
    (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K) (s_K s)))
    (z : rationalPoints Z) :
    splitCocharacterBaseChange (K := inertiaFixedField F) S hS
        (Cartan.centralizerValuation s h z).toAdd =
      (IntegerValuation.centralizerValuation (valuation F) (S := S_K) (s_K s) hK
        (rationalExtend F (inertiaFixedField F) Z z)).toAdd := by
  rw [← IntegerValuation.centralizerValuation_normalized F s h]
  exact IntegerValuation.centralizerValuation_fieldExtend hS
    (FML.normalizedMultiplicativeValuation F) (valuation F) (order_base F) s h hK z

/-- The same exact comparison preserves KP's negative translation. -/
theorem centralizerTranslation_base
    (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K) (s_K s)))
    (z : rationalPoints Z) :
    splitCocharacterBaseChange (K := inertiaFixedField F) S hS
        (Building.centralizerTranslation s h z).toAdd =
      (IntegerValuation.centralizerTranslation (valuation F) (S := S_K) (s_K s) hK
        (rationalExtend F (inertiaFixedField F) Z z)).toAdd := by
  rw [← IntegerValuation.centralizerTranslation_normalized F s h]
  exact IntegerValuation.centralizerTranslation_fieldExtend hS
    (FML.normalizedMultiplicativeValuation F) (valuation F) (order_base F) s h hK z

section Compatibility

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "G_K" => baseChanged F (inertiaFixedField F) G
local notation "i_K" i => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" j => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Full V6 on the actual original points, with the exact existing local
centralizer translation, follows from supplied integer-normalized upstairs V6. -/
theorem isCentralizerCompatible_restrict
    (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K) (s_K s)))
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IntegerValuation.IsCentralizerCompatible (valuation F) (S := S_K)
      (i_K i) (j_K j) (s_K s) hK ψ) :
    Building.IsCentralizerCompatible i j s h
      (RootFunctionFamily.fieldRestrict (k := F) ψ) := by
  apply (IntegerValuation.isCentralizerCompatible_normalized F i j s h _).mp
  exact IntegerValuation.IsCentralizerCompatible.fieldRestrict hS
    (FML.normalizedMultiplicativeValuation F) (valuation F) (order_base F)
    s i j h hK hψ

end Compatibility

section Apartment

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "G_K" => baseChanged F (inertiaFixedField F) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance apartmentExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance apartmentExtendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- The literal image apartment is omega-compatible in the existing local-field
sense on the unchanged original actual centralizer. -/
theorem restrictApartment_isOmegaCompatible
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K)
      (IntegerValuation.order (valuation F)))
    (C : CentralizerDatum i)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K)
      ((GroupScheme.baseChange b).map C.s)))
    (hD : ∀ ψ ∈ D.carrier,
      IntegerValuation.IsCentralizerCompatible (valuation F) (S := S_K) (i_K)
        ((GroupScheme.baseChange b).map C.j)
        ((GroupScheme.baseChange b).map C.s) hK ψ) :
    (restrictApartment i hS hE D).IsOmegaCompatible C := by
  intro φ hφ
  rw [restrictApartment_carrier] at hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact isCentralizerCompatible_restrict hS C.s i C.j C.bijective hK (hD ψ hψ)

/-- Restrict a supplied upstairs apartment together with full V6 to the exact
existing local apartment and original actual centralizer. -/
def restrictOmegaApartment
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K)
      (IntegerValuation.order (valuation F)))
    (C : CentralizerDatum i)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K)
      ((GroupScheme.baseChange b).map C.s)))
    (hD : ∀ ψ ∈ D.carrier,
      IntegerValuation.IsCentralizerCompatible (valuation F) (S := S_K) (i_K)
        ((GroupScheme.baseChange b).map C.j)
        ((GroupScheme.baseChange b).map C.s) hK ψ) :
    {D₀ : KPApartmentData i (localFieldOrder F) // D₀.IsOmegaCompatible C} :=
  ⟨restrictApartment i hS hE D, restrictApartment_isOmegaCompatible i hS hE D C hK hD⟩

@[simp] theorem restrictOmegaApartment_val
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K)
      (IntegerValuation.order (valuation F)))
    (C : CentralizerDatum i)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K)
      ((GroupScheme.baseChange b).map C.s)))
    (hD : ∀ ψ ∈ D.carrier,
      IntegerValuation.IsCentralizerCompatible (valuation F) (S := S_K) (i_K)
        ((GroupScheme.baseChange b).map C.j)
        ((GroupScheme.baseChange b).map C.s) hK ψ) :
    (restrictOmegaApartment i hS hE D C hK hD).val = restrictApartment i hS hE D := rfl

end Apartment

end Langlands.Geometry.Building.MaximalUnramified
