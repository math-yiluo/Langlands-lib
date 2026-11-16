import Langlands.Geometry.Building.UnramifiedRecoveredFacetQuotients
import Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetModels
import Langlands.Geometry.Building.KPZeroDatumExistence
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer

/-! # Rational residue parabolics of constructed maximal Galois facets -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.KPApartmentData

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra
local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1
local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F
local instance : Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).2
local instance : Fintype 𝓀[F] := Fintype.ofFinite _
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

private instance recoveredQuotient_extendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance


local notation "Z" => UnramifiedZeroDatum.ofConnectedReductive
  (baseChanged F (inertiaFixedField F) G) hG
local notation "B" => integerBuildingData D hG hi C h6
local notation "M" => unramifiedIntegerFacetModels Z B

variable (E : GaloisFacet F (inertiaFixedField F) i D hD hG hi C h6)

/-- The original maximal Galois facet has an actual recovered downstairs
reductive quotient with no proper rational parabolics, and every maximal
split torus is central and contained in every maximal torus. All upper
models, image bijections and coefficient compatibilities are constructed. -/
def ConstructedMaximalGaloisFacetResidueStatement : Prop :=
  GeometricallyConnected G.X.hom →
  IsMaximalGaloisFacet F (inertiaFixedField F) i D hD hG hi C h6 E →
  ∃ (N0 : RelativeComponentModelData ↥𝒪[F] F G)
    (_t : UnramifiedComponentModelRecovery N0 ((M).model E.val))
    (Q0 : SpecialFibreQuotientData N0),
    Q0.IsReductiveQuotient ∧
    (∀ (P : GroupScheme (Spec (CommRingCat.of 𝓀[F]))) (p : P ⟶ Q0.quotient),
      IsParabolicSubgroup p → IsIso p) ∧
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of 𝓀[F]))) (s : S.toGrp ⟶ Q0.quotient),
      IsMaximalSplitTorus s →
      ∀ (T' : CommGroupScheme (Spec (CommRingCat.of 𝓀[F]))) (j : T'.toGrp ⟶ Q0.quotient),
        IsMaximalTorus j →
        IsCentral s ∧ ∃ a : S ⟶ T', CommGroupScheme.groupHom a ≫ j = s ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom a)

/-- Actual facet models and the proved facet-parabolic correspondence discharge
the geometric hypotheses of the maximal-Galois-facet residue argument. -/
theorem constructedMaximalGaloisFacetResidue :
    ConstructedMaximalGaloisFacetResidueStatement F i D hD hG hi C h6 E := by
  intro hconn hmax
  have hpoints := unramifiedIntegerFacetModels_full_integralPoints Z B
  obtain ⟨N0, t, Q0, hQ0, hQ, _hsquare, hcompat⟩ :=
    unramifiedFixedFacetRecoveredQuotients F i D hD hG hi C h6 M hpoints E hconn
  let Q := unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E N0 t Q0
  have hbij : (M).HasFacetParabolicOrderBijection E.val Q :=
    unramifiedIntegerFacetModels_hasFacetParabolicOrderBijection Z B E.val Q hQ
  have hres := galoisFacetResidueParabolics F (inertiaFixedField F) i D hD hG hi C h6
    (fixedFieldIntegers F) E M Q 𝓀[F] Q0.quotient (CategoryTheory.Iso.refl _)
    (Langlands.GroupScheme.Descent.FiniteUnramified.fixedResidueAction F) (MaximalUnramified.exists_order_eq_one F)
    hmax hQ hQ0.2.2 hbij hcompat
  exact ⟨N0, t, Q0, hQ0, hres⟩

end Langlands.Geometry.Building.KPApartmentData
