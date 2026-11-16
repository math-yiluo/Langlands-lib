import Langlands.Geometry.Building.UnramifiedRecoveredFacetMaps
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalProof
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Actual recovered reductive quotients at unramified fixed facets -/

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

namespace Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

variable {O k R K : Type u}
  [CommRing O] [IsDomain O] [Field k] [Algebra O k] [IsFractionRing O k]
  [IsLocalRing O]
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of K))}
  {D0 : RelativeComponentModelData O k G}
  {D1 : RelativeComponentModelData R K H}
  [Algebra (ResidueField O) (ResidueField R)]

local notation "b" => Spec.map
  (CommRingCat.ofHom (algebraMap (ResidueField O) (ResidueField R)))

/-- Base change an actual quotient and recover its source through the displayed
special-fibre isomorphism. The quotient itself is the literal base change. -/
def recoveredBaseChange (Q : SpecialFibreQuotientData D0)
    (e : (GroupScheme.baseChange b).obj D0.neutral.specialFibre ≅
      D1.neutral.specialFibre) : SpecialFibreQuotientData D1 where
  radical := (GroupScheme.baseChange b).obj Q.radical
  radicalInclusion := (GroupScheme.baseChange b).map Q.radicalInclusion ≫ e.hom
  quotient := (GroupScheme.baseChange b).obj Q.quotient
  quotient_affine := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd Q.quotient.X.hom b)
    infer_instance
  projection := e.inv ≫ (GroupScheme.baseChange b).map Q.projection

/-- Separable algebraic residue extension and actual source recovery preserve
the represented radical, fppf quotient and connected reductivity. -/
theorem recoveredBaseChange_isReductiveQuotient
    [Algebra.IsSeparable (ResidueField O) (ResidueField R)]
    (Q : SpecialFibreQuotientData D0) (hQ : Q.IsReductiveQuotient)
    (e : (GroupScheme.baseChange b).obj D0.neutral.specialFibre ≅
      D1.neutral.specialFibre) :
    (Q.recoveredBaseChange e).IsReductiveQuotient := by
  let : Smooth D0.neutral.specialFibre.X.hom := by
    let : Smooth D0.neutral.group.X.hom := D0.neutral_smooth
    change Smooth (CategoryTheory.Limits.pullback.snd D0.neutral.group.X.hom
      (IntegralModel.residueBaseMap O))
    infer_instance
  let : IsAffineHom D0.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd D0.neutral.group.X.hom
      (IntegralModel.residueBaseMap O))
    infer_instance
  let : ConnectedSpace D0.neutral.specialFibre.X.left :=
    D0.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D0.neutral_connectedFibres
  refine ⟨(SeparableUnipotentRadical.isUnipotentRadical_baseChange hQ.1).comp_iso e,
    ?_, hQ.2.2.baseChange_of_algebraicExtension⟩
  change RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range ((GroupScheme.baseChange b).map Q.radicalInclusion ≫ e.hom))
    (e.inv ≫ (GroupScheme.baseChange b).map Q.projection)
  rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
  exact hQ.2.1.baseChange b |>.comapIso e

end Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

namespace Langlands.Geometry.Building.KPApartmentData

open Langlands.BruhatTits.IntegralModels
open Langlands.GroupScheme.Descent.FiniteUnramified

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

variable (D0 : RelativeComponentModelData ↥𝒪[F] F G)
  (s : UnramifiedComponentModelRecovery D0 (M.model E.val))
  (Q0 : SpecialFibreQuotientData D0)

/-- Choose the actual upstairs quotient as the literal residue base change of
an actual downstairs quotient, with projection through neutral model recovery. -/
def unramifiedFixedFacetRecoveredQuotient :
    SpecialFibreQuotientData (M.model E.val) :=
  Q0.recoveredBaseChange
    (IntegralModel.residueRecoveryIso D0.neutral 𝓡 𝕂 s.neutralIso
      (algebraBaseMap 𝓀[F] L) (fixedResidueBaseMap_square F))

/-- The actual recovered quotient has exactly the recovered downstairs
projection. -/
theorem unramifiedFixedFacetRecoveredQuotient_projection :
    (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E D0 s Q0).projection =
      unramifiedFixedFacetDescendedMap F i D hD hG hi C h6 M E D0 s Q0.projection := rfl

/-- The canonical residue extension is algebraic and separable, so validity of
the downstairs quotient implies validity of the actual recovered quotient. -/
theorem unramifiedFixedFacetRecoveredQuotient_isReductiveQuotient
    (hQ0 : Q0.IsReductiveQuotient) :
    (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E D0 s Q0).IsReductiveQuotient :=
  Q0.recoveredBaseChange_isReductiveQuotient hQ0
    (IntegralModel.residueRecoveryIso D0.neutral 𝓡 𝕂 s.neutralIso
      (algebraBaseMap 𝓀[F] L) (fixedResidueBaseMap_square F))

/-- The actual recovered projection satisfies the original canonical
coefficient square; its quotient identification is the identity. -/
theorem unramifiedFixedFacetRecoveredQuotient_square :
    UnramifiedFixedFacetResidueQuotientSquare F i D hD hG hi C h6 M hpoints E
      (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E D0 s Q0)
      Q0.quotient (CategoryTheory.Iso.refl _) := by
  intro σ
  simpa only [CategoryTheory.Iso.refl_hom, Category.comp_id,
    unramifiedFixedFacetRecoveredQuotient_projection] using
    unramifiedFixedFacetDescendedMap_naturality F i D hD hG hi C h6 M hpoints E
      D0 s Q0.projection σ

include hpoints in
/-- Actual all-test images of incident facets in the constructed quotient
satisfy covariance under the canonical residue coefficient action. -/
theorem unramifiedFixedFacetRecoveredQuotient_imageCompatibility :
    HasGaloisResidueImageCompatibility F 𝕂 i D hD hG hi C h6 𝓡 E M
      (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E D0 s Q0)
      𝓀[F] Q0.quotient (CategoryTheory.Iso.refl _) (fixedResidueAction F) :=
  (unramifiedFacetResidueComparisons F i D hD hG hi C h6 M hpoints E
    (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E D0 s Q0)
    Q0.quotient (CategoryTheory.Iso.refl _)
    (unramifiedFixedFacetRecoveredQuotient_square F i D hD hG hi C h6 M hpoints E
      D0 s Q0)).2

/-- An original fixed facet has an actual downstairs reductive quotient whose
literal recovered upstairs quotient is valid and has the canonical coefficient
square and all-test incident-image covariance. -/
def UnramifiedFixedFacetRecoveredQuotientStatement : Prop :=
  GeometricallyConnected G.X.hom →
    ∃ (N0 : RelativeComponentModelData ↥𝒪[F] F G)
      (t : UnramifiedComponentModelRecovery N0 (M.model E.val))
      (P0 : SpecialFibreQuotientData N0),
      P0.IsReductiveQuotient ∧
      (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E N0 t P0).IsReductiveQuotient ∧
      UnramifiedFixedFacetResidueQuotientSquare F i D hD hG hi C h6 M hpoints E
        (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E N0 t P0)
        P0.quotient (CategoryTheory.Iso.refl _) ∧
      HasGaloisResidueImageCompatibility F 𝕂 i D hD hG hi C h6 𝓡 E M
        (unramifiedFixedFacetRecoveredQuotient F i D hD hG hi C h6 M E N0 t P0)
        𝓀[F] P0.quotient (CategoryTheory.Iso.refl _) (fixedResidueAction F)

omit [IsAffineHom G.X.hom] in
private theorem exists_downstairsQuotient
    (N0 : RelativeComponentModelData ↥𝒪[F] F G) :
    ∃ P0 : SpecialFibreQuotientData N0, P0.IsReductiveQuotient := by
  let : PerfectField (ResidueField ↥𝒪[F]) :=
    inferInstanceAs (PerfectField 𝓀[F])
  exact SpecialFibreQuotientData.exists_isReductiveQuotient
    (R := ↥𝒪[F]) (K := F) (G := G) N0

/-- Construct recovery and the downstairs quotient, then prove validity and
coefficient covariance for its actual recovered upstairs quotient. -/
theorem unramifiedFixedFacetRecoveredQuotients :
    UnramifiedFixedFacetRecoveredQuotientStatement F i D hD hG hi C h6 M hpoints E := by
  intro hconn
  obtain ⟨N0, ⟨t⟩⟩ :=
    exists_unramifiedFixedFacetRecovery F i D hD hG hi C h6 M hpoints E hconn
  let P0 : SpecialFibreQuotientData N0 := Classical.choose (exists_downstairsQuotient F N0)
  have hP0 : P0.IsReductiveQuotient := Classical.choose_spec (exists_downstairsQuotient F N0)
  exact ⟨N0, t, P0, hP0,
    unramifiedFixedFacetRecoveredQuotient_isReductiveQuotient F i D hD hG hi C h6 M E
      N0 t P0 hP0,
    unramifiedFixedFacetRecoveredQuotient_square F i D hD hG hi C h6 M hpoints E N0 t P0,
    unramifiedFixedFacetRecoveredQuotient_imageCompatibility F i D hD hG hi C h6 M
      hpoints E N0 t P0⟩

end Langlands.Geometry.Building.KPApartmentData
