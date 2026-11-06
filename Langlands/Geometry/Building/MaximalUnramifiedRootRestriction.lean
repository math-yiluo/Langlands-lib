import Langlands.Geometry.Building.RootApartmentFieldDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Exact local normalization for actual unramified root restriction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The real additive unit character of the constructed normalized valuation
on the actual inertia fixed field. -/
def realOrderCharacter : (inertiaFixedField F)ˣ →* Multiplicative ℝ :=
  (Int.castAddHom ℝ).toMultiplicative.comp (IntegerValuation.orderUnits (valuation F))

@[simp] theorem realOrderCharacter_toAdd (t : (inertiaFixedField F)ˣ) :
    (realOrderCharacter F t).toAdd = IntegerValuation.order (valuation F) t := rfl

/-- The original local field order is preserved exactly, with no rescaling. -/
@[simp] theorem realOrderCharacter_base (t : Fˣ) :
    (realOrderCharacter F (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom t)).toAdd =
      localFieldOrder F t :=
  order_base_eq_localFieldOrder F t

/-- Nontriviality on original units is proved using the existing original
order-one uniformizer, rather than supplied as a separate restriction premise. -/
theorem realOrderCharacter_nontrivial_on_base :
    ∃ t : Fˣ, (realOrderCharacter F
      (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom t)).toAdd ≠ 0 := by
  refine ⟨SplitTorusValuation.uniformizerUnit F, ?_⟩
  rw [realOrderCharacter_base, localFieldOrder,
    SplitTorusValuation.fieldOrderUnits_uniformizerUnit]
  norm_num

variable {F}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap F (inertiaFixedField F)
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged F (inertiaFixedField F) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- Literal root valuation restriction from the actual inertia fixed field.
No V3 or unit nontriviality premise remains. -/
def restrictRootValuation
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) (i_K) ψ)
    (hcompat : IsSplitTorusCompatible (S := S_K) (i_K)
      (IntegerValuation.order (valuation F)) ψ) :
    {φ : RootFunctionFamily S G // IsRootDatumValuation i φ} :=
  hψ.fieldRestrictValuation i hS hE (realOrderCharacter F) hcompat
    (realOrderCharacter_nontrivial_on_base F)

@[simp] theorem restrictRootValuation_val
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) (i_K) ψ)
    (hcompat : IsSplitTorusCompatible (S := S_K) (i_K)
      (IntegerValuation.order (valuation F)) ψ) :
    (restrictRootValuation i hS hE hψ hcompat).val =
      RootFunctionFamily.fieldRestrict (k := F) ψ := rfl

/-- The constructed root family is compatible with precisely the existing
localFieldOrder on the original field units. -/
theorem restrictRootValuation_compatible
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) (i_K) ψ)
    (hcompat : IsSplitTorusCompatible (S := S_K) (i_K)
      (IntegerValuation.order (valuation F)) ψ) :
    IsSplitTorusCompatible i (localFieldOrder F)
      (restrictRootValuation i hS hE hψ hcompat).val := by
  have h := RootFunctionFamily.fieldRestrict_isSplitTorusCompatible hS hcompat
  simpa only [restrictRootValuation_val, order_base_eq_localFieldOrder] using h

/-- Restrict a supplied upstairs apartment to the actual original group,
with exactly its existing normalized local field order. -/
def restrictApartment
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K)
      (IntegerValuation.order (valuation F))) :
    KPApartmentData i (localFieldOrder F) where
  carrier := (KPApartmentData.fieldRestrict i hS hE (realOrderCharacter F)
    (realOrderCharacter_nontrivial_on_base F) D).carrier
  exists_eq_orbit := by
    obtain ⟨ψ, hψ, hcompat, hcarrier⟩ :=
      (KPApartmentData.fieldRestrict i hS hE (realOrderCharacter F)
        (realOrderCharacter_nontrivial_on_base F) D).exists_eq_orbit
    exact ⟨ψ, hψ, by simpa only [realOrderCharacter_base] using hcompat, hcarrier⟩
  smul_mem := (KPApartmentData.fieldRestrict i hS hE (realOrderCharacter F)
    (realOrderCharacter_nontrivial_on_base F) D).smul_mem

@[simp] theorem restrictApartment_carrier
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K)
      (IntegerValuation.order (valuation F))) :
    (restrictApartment i hS hE D).carrier =
      RootFunctionFamily.fieldRestrict (k := F) '' D.carrier := rfl

end Langlands.Geometry.Building.MaximalUnramified
