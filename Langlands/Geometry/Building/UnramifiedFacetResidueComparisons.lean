import Langlands.Geometry.Building.GaloisFacetResidueComparisons
import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable
import Langlands.GroupScheme.Descent.FiniteUnramifiedAutomorphismLift

/-! # Canonical maximal-unramified facet residue comparisons -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

local instance fixedResidueAlgebra : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

/-- The automorphism of the actual residue field induced by the canonical
integer automorphism fixes the original residue field. -/
def fixedResidueAut (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    ResidueField (fixedFieldIntegers F) ≃ₐ[𝓀[F]] ResidueField (fixedFieldIntegers F) where
  __ := ResidueField.mapEquiv (fixedFieldIntegerAut F σ)
  commutes' x := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    change residue (fixedFieldIntegers F)
      (fixedFieldIntegerAut F σ (integerToFixedField F x)) =
        residue (fixedFieldIntegers F) (integerToFixedField F x)
    apply congrArg (residue (fixedFieldIntegers F))
    apply Subtype.ext
    exact σ.commutes (x : F)

@[simp] theorem fixedResidueAut_residue
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (x : fixedFieldIntegers F) :
    fixedResidueAut F σ (residue (fixedFieldIntegers F) x) =
      residue (fixedFieldIntegers F) (fixedFieldIntegerAut F σ x) := rfl

/-- Actual field automorphisms act on the actual residue field, over the base
residue field, by their induced integer automorphisms. -/
def fixedResidueAction : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
    (ResidueField (fixedFieldIntegers F) ≃ₐ[𝓀[F]] ResidueField (fixedFieldIntegers F)) where
  toFun := fixedResidueAut F
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    change residue (fixedFieldIntegers F) (fixedFieldIntegerAut F 1 x) =
      residue (fixedFieldIntegers F) x
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    change residue (fixedFieldIntegers F) (fixedFieldIntegerAut F (σ * τ) x) =
      residue (fixedFieldIntegers F)
        (fixedFieldIntegerAut F σ (fixedFieldIntegerAut F τ x))
    rfl

/-- The canonical residue and integer coefficient maps form the literal square
needed to specialize the original neutral model comparison. -/
theorem fixedResidueAction_square
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    galoisBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)) (fixedResidueAction F σ) ≫
        IntegralModel.residueBaseMap (fixedFieldIntegers F) =
      IntegralModel.residueBaseMap (fixedFieldIntegers F) ≫ fixedIntegerBaseAut F σ := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  rfl

end Langlands.GroupScheme.Descent.FiniteUnramified

namespace Langlands.Geometry.Building.KPApartmentData

open Langlands.BruhatTits.IntegralModels
open Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra
local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1
local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F
local instance : IsAlgClosed (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

variable
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i).hom.hom.left]
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) T)
    (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (hD : GaloisStable F (inertiaFixedField F) i D)
  (hG : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hi : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) T)
    (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) T)
    (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

private instance unramifiedComparison_extendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable
  (M : IntegerFacetModelData (K := inertiaFixedField F)
    (G := baseChanged F (inertiaFixedField F) G) (v := MaximalUnramified.valuation F)
    (integerBuildingData D hG hi C h6) (fixedFieldIntegers F))
  (hpoints : ∀ E : (integerBuildingData D hG hi C h6).BuildingFacet,
    (M.model E).full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      (integerBuildingData D hG hi C h6).pointwiseFixer E.val)
  (E : GaloisFacet F (inertiaFixedField F) i D hD hG hi C h6)

local notation "𝕂" => inertiaFixedField F
local notation "𝓡" => fixedFieldIntegers F
local notation "L" => ResidueField (fixedFieldIntegers F)
local notation "incAct" => galoisIncidentFacetAction F 𝕂 i D hD hG hi C h6 E

/-- Specialize the actual incident source comparison using only the canonical
integer and residue actions and the proved valuation invariance. -/
abbrev unramifiedIncidentResidueIso (σ : 𝕂 ≃ₐ[F] 𝕂)
    (J : (integerBuildingData D hG hi C h6).IncidentFacets E.val) :=
  incidentResidueGaloisIso F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) 𝓀[F] (fixedResidueAction F)
    (fixedResidueAction_square F) σ J

/-- The canonical coefficient comparison on the original fixed facet. -/
abbrev unramifiedFixedFacetResidueIso (σ : 𝕂 ≃ₐ[F] 𝕂) :=
  fixedFacetResidueGaloisIso F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) 𝓀[F] (fixedResidueAction F)
    (fixedResidueAction_square F) σ

/-- Canonical coefficient specialization preserves the literal original
incidence square. -/
theorem unramifiedIncidentResidueIso_naturality (σ : 𝕂 ≃ₐ[F] 𝕂)
    (J : (integerBuildingData D hG hi C h6).IncidentFacets E.val) :
    (unramifiedIncidentResidueIso F i D hD hG hi C h6 M hpoints E σ J).hom ≫
        (M.morphism E.val (incAct σ J).val (incAct σ J).property).neutralSpecialFibreMap =
      (GroupScheme.baseChange (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))).map
          (M.morphism E.val J.val J.property).neutralSpecialFibreMap ≫
        (unramifiedFixedFacetResidueIso F i D hD hG hi C h6 M hpoints E σ).hom :=
  incidentResidueGaloisIso_naturality F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) 𝓀[F] (fixedResidueAction F)
    (fixedResidueAction_square F) σ J

variable
  (Q : SpecialFibreQuotientData (R := fixedFieldIntegers F) (K := inertiaFixedField F)
    (G := baseChanged F (inertiaFixedField F) G) (M.model E.val))
  (H : GroupScheme (Spec (CommRingCat.of 𝓀[F]))) [IsAffineHom H.X.hom]
  (e : Q.quotient ≅ baseChanged 𝓀[F] (ResidueField (fixedFieldIntegers F)) H)

/-- The remaining quotient obligation uses the constructed canonical
comparison on the actual neutral special fibre of the original facet. -/
def UnramifiedFixedFacetResidueQuotientSquare : Prop :=
  ∀ σ : 𝕂 ≃ₐ[F] 𝕂,
    (unramifiedFixedFacetResidueIso F i D hD hG hi C h6 M hpoints E σ).hom ≫
        Q.projection ≫ e.hom =
      (GroupScheme.baseChange (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))).map
          (Q.projection ≫ e.hom) ≫
        (descentBaseChangeIso (algebraBaseMap 𝓀[F] L)
          (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))
          (galoisBaseMap_over 𝓀[F] L (fixedResidueAction F σ)) H).hom

/-- Construct all actual residue comparison data from full model point images
and the separate quotient square; no coefficient maps or stability are supplied. -/
def unramifiedResidueCoefficientComparisons
    (hquot : UnramifiedFixedFacetResidueQuotientSquare F i D hD hG hi C h6 M
      hpoints E Q H e) :
    ResidueCoefficientComparisonData F 𝕂 i D hD hG hi C h6 𝓡 E M Q 𝓀[F] H e
      (fixedResidueAction F) :=
  residueCoefficientComparisonsOfQuotientSquare F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) 𝓀[F] (fixedResidueAction F)
    (fixedResidueAction_square F) Q H e hquot

/-- Canonical coefficient specialization leaves just the quotient square
before the actual all-test residue image covariance follows. -/
def UnramifiedFacetResidueComparisonsStatement : Prop :=
  UnramifiedFixedFacetResidueQuotientSquare F i D hD hG hi C h6 M hpoints E Q H e →
    Nonempty (ResidueCoefficientComparisonData F 𝕂 i D hD hG hi C h6 𝓡 E M Q 𝓀[F]
      H e (fixedResidueAction F)) ∧
    HasGaloisResidueImageCompatibility F 𝕂 i D hD hG hi C h6 𝓡 E M Q 𝓀[F]
      H e (fixedResidueAction F)

/-- The strict integer-ring arithmetic and both coefficient squares are
proved inputs, so only the explicitly separate quotient square remains. -/
theorem unramifiedFacetResidueComparisons :
    UnramifiedFacetResidueComparisonsStatement F i D hD hG hi C h6 M hpoints E Q H e := by
  intro hquot
  let c := unramifiedResidueCoefficientComparisons F i D hD hG hi C h6 M hpoints E
    Q H e hquot
  exact ⟨⟨c⟩, hasGaloisResidueImageCompatibility_of_coefficientComparisons
    F 𝕂 i D hD hG hi C h6 𝓡 E M Q 𝓀[F] H e (fixedResidueAction F) c⟩

end Langlands.Geometry.Building.KPApartmentData
