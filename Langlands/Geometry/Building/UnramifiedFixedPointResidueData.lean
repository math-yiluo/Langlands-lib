import Langlands.Geometry.Building.ConstructedMaximalGaloisFacetResidue

/-! # Actual residue data fixing a prescribed coefficient-fixed building point -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.KPApartmentData

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
private local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
private local instance : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra
private local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1
private local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F
private local instance : Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).2
private local instance : Fintype 𝓀[F] := Fintype.ofFinite _
private local instance : IsAlgClosed (ResidueField (fixedFieldIntegers F)) :=
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

private instance recoveredQuotient_extendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance


local notation "Z" => UnramifiedZeroDatum.ofConnectedReductive
  (baseChanged F (inertiaFixedField F) G) hG
local notation "B" => integerBuildingData D hG hi C h6
local notation "M" => unramifiedIntegerFacetModels Z B


/-- At each prescribed coefficient-fixed point, construct actual lower model
and residue quotient data with neutral unramified integral points fixing that
point and no proper rational residue parabolics. -/
def UnramifiedFixedPointResidueDataStatement : Prop :=
  GeometricallyConnected G.X.hom →
  ∀ y : D.ReducedBuilding, IsGaloisFixed F (inertiaFixedField F) i D hD y →
  ∃ (E : GaloisFacet F (inertiaFixedField F) i D hD hG hi C h6)
    (N0 : RelativeComponentModelData ↥𝒪[F] F G)
    (_t : UnramifiedComponentModelRecovery N0 ((M).model E.val))
    (Q0 : SpecialFibreQuotientData N0),
    IsMaximalGaloisFacet F (inertiaFixedField F) i D hD hG hi C h6 E ∧
    y ∈ galoisFacetClosure F (inertiaFixedField F) i D hD hG hi C h6 E ∧
    (∃ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      E.val.val ⊆ g • (B).apartmentImage ∧
      galoisFacetClosure F (inertiaFixedField F) i D hD hG hi C h6 E ⊆
        g • (B).apartmentImage) ∧
    Q0.IsReductiveQuotient ∧
    N0.neutral.baseChangeUnramified.integralPoints ≤ D.reducedFixer y ∧
    (∀ (P : GroupScheme (Spec (CommRingCat.of 𝓀[F]))) (p : P ⟶ Q0.quotient),
      IsParabolicSubgroup p → IsIso p) ∧
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of 𝓀[F]))) (s : S.toGrp ⟶ Q0.quotient),
      IsMaximalSplitTorus s →
      ∀ (T' : CommGroupScheme (Spec (CommRingCat.of 𝓀[F]))) (j : T'.toGrp ⟶ Q0.quotient),
        IsMaximalTorus j →
        IsCentral s ∧ ∃ a : S ⟶ T', CommGroupScheme.groupHom a ≫ j = s ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom a)

/-- The constructed facet models and their actual residue quotient give the
prescribed-point fixation input for the remaining integral split-source lift. -/
theorem unramifiedFixedPointResidueData :
    UnramifiedFixedPointResidueDataStatement F i D hD hG hi C h6 := by
  intro hconn y hy
  obtain ⟨E, hmax, hyE, g, hEap, hclap⟩ := exists_maximal_galoisFacet_apartment
    F (inertiaFixedField F) i D hD hG hi C h6 y hy
  obtain ⟨N0, t, Q0, hQ0, hno, hcentral⟩ := constructedMaximalGaloisFacetResidue
    F i D hD hG hi C h6 E hconn hmax
  have hycl : y ∈ (B).buildingFacetClosure E.val :=
    ((galoisFacetClosure_eq_inter F (inertiaFixedField F) i D hD hG hi C h6 E).subset hyE).1
  have hfixer : (B).pointwiseFixer E.val.val ≤ D.reducedFixer y := by
    intro a ha
    have hacl : a ∈ (B).pointwiseFixer ((B).buildingFacetClosure E.val) := by
      rwa [(B).pointwiseFixer_buildingFacetClosure E.val]
    exact D.mem_reducedFixer.mpr (D.mem_pointwiseFixer.mp hacl y hycl)
  have hneutral : N0.neutral.baseChangeUnramified.integralPoints ≤ D.reducedFixer y := by
    rw [t.neutral_integralPoints_eq,
      unramifiedIntegerFacetModels_neutral_integralPoints Z B E.val]
    exact inf_le_right.trans hfixer
  exact ⟨E, N0, t, Q0, hmax, hyE, ⟨g, hEap, hclap⟩,
    hQ0, hneutral, hno, hcentral⟩

end Langlands.Geometry.Building.KPApartmentData
