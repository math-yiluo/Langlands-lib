import Langlands.GroupScheme.IntegralModel.CoefficientSpecialFibreTorus
import Langlands.GroupScheme.Torus.MaximalTorusImageSplitLift
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus

/-! # Original-residue torus preservation from an unramified apartment -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  integerToFixedField_isLocalHom F

local instance : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F

local instance : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

local instance : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).isAlgClosed

local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

-- The intrinsic value group lies in Type u, as required by the coefficient theorem.
local instance : ValuativeRel (inertiaFixedField F) :=
  ValuativeRel.ofValuation (fixedFieldValued F).v

section Models

variable {M N : IntegralModel ↥𝒪[F] F G}
  [Smooth M.group.X.hom] [Smooth N.group.X.hom]
  [ConnectedSpace M.specialFibre.X.left]
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (Ω : Set C.Apartment)
  (hpts : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤
    M.baseChangeUnramified.integralPoints)
  (φ : M.Hom N (𝟙 G))

include C E Ω hpts

/-- The actual apartment bound upstairs preserves every maximal torus over the
original residue field through the actual original-model residue map. -/
theorem isMaximalTorus_specialFibreMap_of_unramified_apartment
    {T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F])))}
    {i : T.toGrp ⟶ M.specialFibre} (hi : IsMaximalTorus i) :
    IsMaximalTorus (i ≫ φ.specialFibreMap) := by
  have heq : (ValuativeRel.valuation (inertiaFixedField F)).IsEquiv
      (MaximalUnramified.valuation F) := by
    intro x y
    change _ ≤ _ ↔ MaximalUnramified.valueGroupEquiv F _ ≤
      MaximalUnramified.valueGroupEquiv F _
    rw [map_le_map_iff]
  have hb := (map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω).trans hpts
  rw [← characterValuationKernel_eq_of_isEquiv heq C.S.toGrp] at hb
  dsimp only [IntegralModel.baseChangeUnramified] at hb
  exact φ.isMaximalTorus_specialFibreMap_of_coefficient_bounded
    (R := ↥𝒪[F]) (K := F) (A := fixedFieldIntegers F) (L := inertiaFixedField F)
    (T := C.S) (iT := C.i)
    C.isConnectedReductive (ValuativeRel.valuation (inertiaFixedField F))
    (fun a => heq.eq_one_iff_eq_one.mpr
      (SpecialTorusIntegralModel.valuation_units_eq_one F a))
    C.isMaximalSplitTorus hb hi

/-- The common torus can be chosen over the original residue field. -/
theorem exists_maximalTorus_specialFibreMap_of_unramified_apartment :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
      (i : T.toGrp ⟶ M.specialFibre),
      IsMaximalTorus i ∧ IsMaximalTorus (i ≫ φ.specialFibreMap) := by
  let : Smooth M.specialFibre.X.hom := by
    change Smooth (pullback.snd M.group.X.hom (residueBaseMap ↥𝒪[F]))
    infer_instance
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap ↥𝒪[F]))
    infer_instance
  obtain ⟨T, i, hi⟩ := maximalTorusExistence (IsLocalRing.ResidueField ↥𝒪[F]) M.specialFibre
  exact ⟨T, i, hi,
    isMaximalTorus_specialFibreMap_of_unramified_apartment C E Ω hpts φ hi⟩

/-- Every torus, including a nonsplit one, has a closed composite through the
original special-fibre map. -/
theorem isClosedSubgroup_specialFibreMap_of_unramified_apartment
    {T : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F])))}
    {i : T ⟶ M.specialFibre} (hT : IsTorus T) (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (i ≫ φ.specialFibreMap) := by
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap ↥𝒪[F]))
    infer_instance
  let : LocallyOfFiniteType M.specialFibre.X.hom := by
    change LocallyOfFiniteType (pullback.snd M.group.X.hom (residueBaseMap ↥𝒪[F]))
    infer_instance
  let Tc : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))) :=
    { T with comm := hT.isCommMonObj }
  exact IsClosedSubgroup.comp_of_maximalTorus_images (T := Tc) φ.specialFibreMap
    (fun _ _ hs => isMaximalTorus_specialFibreMap_of_unramified_apartment C E Ω hpts φ hs)
    hi hT

end Models

namespace RelativeComponentModelHom

variable {D₀ D₁ : RelativeComponentModelData ↥𝒪[F] F G}
  (φ : RelativeComponentModelHom D₀ D₁)

/-- For actual neutral component models, connectedness of the source residue
fibre follows from connected fibres, and the apartment bound gives the torus
preamble of KP Axiom 4.1.22. -/
theorem preservesTori_of_unramified_apartment
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Ω : Set C.Apartment)
    (hpts : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤
      D₀.neutral.baseChangeUnramified.integralPoints) :
    φ.PreservesTori := by
  let : Smooth D₀.neutral.group.X.hom := D₀.neutral_smooth
  let : Smooth D₁.neutral.group.X.hom := D₁.neutral_smooth
  let : ConnectedSpace D₀.neutral.specialFibre.X.left :=
    D₀.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D₀.neutral_connectedFibres
  intro T i hT hi
  exact isClosedSubgroup_specialFibreMap_of_unramified_apartment C E Ω hpts φ.neutral hT hi

end RelativeComponentModelHom

/-- The actual unramified apartment bound forces original-residue maximal-torus
preservation, original-residue existence, and closedness for every torus. -/
def UnramifiedApartmentTorusPreservationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Ω : Set C.Apartment)
    (M N : IntegralModel ↥𝒪[F] F G)
    [Smooth M.group.X.hom] [Smooth N.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left] (φ : M.Hom N (𝟙 G)),
    E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤
        M.baseChangeUnramified.integralPoints →
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
      (i : T.toGrp ⟶ M.specialFibre),
      IsMaximalTorus i → IsMaximalTorus (i ≫ φ.specialFibreMap)) ∧
    (∃ (T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
      (i : T.toGrp ⟶ M.specialFibre),
      IsMaximalTorus i ∧ IsMaximalTorus (i ≫ φ.specialFibreMap)) ∧
    (∀ (T : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
      (i : T ⟶ M.specialFibre),
      IsTorus T → IsClosedSubgroup i → IsClosedSubgroup (i ≫ φ.specialFibreMap))

set_option maxHeartbeats 600000 in
/-- Apply the apartment unit bound with canonical coefficient arithmetic, then
extend arbitrary closed tori to maximal tori over the original residue field. -/
theorem unramifiedApartmentTorusPreservation :
    UnramifiedApartmentTorusPreservationStatement.{u} := by
  intro F _ _ _ _ G _ C E Ω M N _ _ _ φ hpts
  refine ⟨?_, ?_, ?_⟩
  · intro T i hi
    exact isMaximalTorus_specialFibreMap_of_unramified_apartment
      (F := F) (G := G) (M := M) (N := N) C E Ω hpts φ (T := T) (i := i) hi
  · exact exists_maximalTorus_specialFibreMap_of_unramified_apartment
      (F := F) (G := G) (M := M) (N := N) C E Ω hpts φ
  · intro T i hT hi
    exact isClosedSubgroup_specialFibreMap_of_unramified_apartment
      (F := F) (G := G) (M := M) (N := N) C E Ω hpts φ (T := T) (i := i) hT hi

end Langlands.BruhatTits.IntegralModels
