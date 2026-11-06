import Langlands.Shimura.PEL.HarrisTaylorCMGeometricSourceDerivedScalars

/-! # Derived source changes of scalar-restricted exact geometric CM diagrams -/

noncomputable section

universe wC wS wK wL wM

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

private theorem singleComparison_square
    {CL CK CM DL DK DM : Type*}
    [Category* CL] [Category* CK] [Category* CM]
    [Category* DL] [Category* DK] [Category* DM]
    (SL : CL ⥤ DL) (SK : CK ⥤ DK) (SM : CM ⥤ DM)
    (R : CL ⥤ CM) (Q : CK ⥤ CM) (DR : DL ⥤ DM) (DQ : DK ⥤ DM)
    (sR : SL ⋙ DR ≅ R ⋙ SM) (sQ : SK ⋙ DQ ≅ Q ⋙ SM)
    {BL AL : CL} {BK AK : CK} {AL' : DL} {AK' : DK}
    (cL : BL ≅ AL) (cK : BK ≅ AK)
    (bL : AL' ≅ SL.obj AL) (bK : AK' ≅ SK.obj AK)
    (bLhom : AL' ⟶ SL.obj AL) (bKinv : SK.obj AK ⟶ AK')
    (hbL : bLhom = bL.hom) (hbK : bKinv = bK.inv)
    (eB : R.obj BL ≅ Q.obj BK) (eA : R.obj AL ≅ Q.obj AK)
    (cL' : SL.obj BL ⟶ AL') (cK' : SK.obj BK ⟶ AK')
    (eB' : DR.obj (SL.obj BL) ⟶ DQ.obj (SK.obj BK))
    (eA' : DR.obj AL' ⟶ DQ.obj AK')
    (hL : cL' = SL.map cL.hom ≫ bL.inv)
    (hK : cK' = SK.map cK.hom ≫ bK.inv)
    (hB : eB' = sR.hom.app BL ≫ SM.map eB.hom ≫ sQ.inv.app BK)
    (hA : eA' = DR.map bLhom ≫ sR.hom.app AL ≫ SM.map eA.hom ≫
      sQ.inv.app AK ≫ DQ.map bKinv)
    (h : R.map cL.hom ≫ eA.hom = eB.hom ≫ Q.map cK.hom) :
    DR.map cL' ≫ eA' = eB' ≫ DQ.map cK' := by
  rw [hL, hK, hB, hA, hbL, hbK]
  have hR : DR.map (SL.map cL.hom) ≫ sR.hom.app AL =
      sR.hom.app BL ≫ SM.map (R.map cL.hom) := sR.hom.naturality cL.hom
  have hQ : SM.map (Q.map cK.hom) ≫ sQ.inv.app AK =
      sQ.inv.app BK ≫ DQ.map (SK.map cK.hom) := sQ.inv.naturality cK.hom
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% hR]
  rw [← SM.map_comp_assoc, h, SM.map_comp, Category.assoc]
  rw [reassoc_of% hQ]

private theorem comparisonSquare_comp
    {CL CK CM : Type*} [Category* CL] [Category* CK] [Category* CM]
    (R : CL ⥤ CM) (Q : CK ⥤ CM)
    {BL AL TL : CL} {BK AK TK : CK}
    (cL : BL ⟶ AL) (cK : BK ⟶ AK) (tL : AL ⟶ TL) (tK : AK ⟶ TK)
    (eB : R.obj BL ⟶ Q.obj BK) (eA : R.obj AL ⟶ Q.obj AK)
    (eT : R.obj TL ⟶ Q.obj TK)
    (hc : R.map cL ≫ eA = eB ≫ Q.map cK)
    (ht : R.map tL ≫ eT = eA ≫ Q.map tK) :
    R.map (cL ≫ tL) ≫ eT = eB ≫ Q.map (cK ≫ tK) := by
  rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc, hc,
    Category.assoc, ← Functor.map_comp]

private theorem exactSingleComparison_square
    {CA CL CK CM : Type*}
    [Category* CA] [Category* CL] [Category* CK] [Category* CM]
    [Abelian CA] [Abelian CL] [Abelian CK] [Abelian CM]
    [HasDerivedCategory.{wC} CA] [HasDerivedCategory.{wL} CL]
    [HasDerivedCategory.{wK} CK] [HasDerivedCategory.{wM} CM]
    (FL : CA ⥤ CL) [FL.Additive] [PreservesFiniteLimits FL] [PreservesFiniteColimits FL]
    (FK : CA ⥤ CK) [FK.Additive] [PreservesFiniteLimits FK] [PreservesFiniteColimits FK]
    (R : CL ⥤ CM) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (Q : CK ⥤ CM) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (eA : FL ⋙ R ≅ FK ⋙ Q) (M : CA)
    {BL : CL} {BK : CK} (cL : BL ≅ FL.obj M) (cK : BK ≅ FK.obj M)
    (eB : R.obj BL ≅ Q.obj BK)
    (h : R.map cL.hom ≫ eA.hom.app M = eB.hom ≫ Q.map cK.hom) (d : ℤ) :
    R.mapDerivedCategory.map
        (((DerivedCategory.singleFunctor CL d).mapIso cL ≪≫
          ((FL.mapDerivedCategorySingleFunctor d).app M).symm).hom) ≫
        (Langlands.Cohomology.exactDerivedSquareIso FL FK R Q eA).hom.app
          ((DerivedCategory.singleFunctor CA d).obj M) =
      (((R.mapDerivedCategorySingleFunctor d).app BL ≪≫
        (DerivedCategory.singleFunctor CM d).mapIso eB ≪≫
        ((Q.mapDerivedCategorySingleFunctor d).app BK).symm).hom) ≫
      Q.mapDerivedCategory.map
        (((DerivedCategory.singleFunctor CK d).mapIso cK ≪≫
          ((FK.mapDerivedCategorySingleFunctor d).app M).symm).hom) := by
  exact singleComparison_square
    (DerivedCategory.singleFunctor CL d) (DerivedCategory.singleFunctor CK d)
    (DerivedCategory.singleFunctor CM d) R Q R.mapDerivedCategory Q.mapDerivedCategory
    (R.mapDerivedCategorySingleFunctor d) (Q.mapDerivedCategorySingleFunctor d)
    cL cK ((FL.mapDerivedCategorySingleFunctor d).app M)
    ((FK.mapDerivedCategorySingleFunctor d).app M)
    ((FL.mapDerivedCategorySingleFunctor d).hom.app M)
    ((FK.mapDerivedCategorySingleFunctor d).inv.app M) rfl rfl
    eB (eA.app M) _ _ _ _ rfl rfl rfl
    (Langlands.Cohomology.exactDerivedSquareIso_hom_app_single FL FK R Q eA M d) h

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Sheaf Langlands.Cohomology

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

local notation "schemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "X" => Functor.obj (schemes q) U
local notation "J" => Scheme.smallEtaleTopology X
local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

local notation "system" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "source" k => cmHarrisGeometricAssociatedCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "constantSource" k => cmHarrisGeometricConstantCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "sourceTrivialization" k => cmHarrisGeometricAssociatedCoefficientSourceTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "groups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "coefficientCategory" => EquivariantDiagram groups (ModuleCat.{0} Rcoeff)
local notation "sourceCategory" k =>
  (Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} Rcoeff))
local notation "mixedCategory" k "," l =>
  (Under l ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} Rcoeff))
local notation "associatedSourceFunctor" k =>
  etaleAssociatedSourceSystemFunctor X covers coverProperty k
local notation "constantSourceFunctor" k => etaleConstantSourceSystemFunctor X covers k
local notation "derivedCoefficient" d =>
  (DerivedCategory.singleFunctor coefficientCategory d).obj coefficients

local notation "restrictedSource" k => cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "sourceComparison" k => cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "restrictedTrivialization" k =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U ρ p m hm existence geometry hRigid k

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

variable [HasDerivedCategory.{wC}
  (EquivariantDiagram (cmHarrisCoefficientGroups D ρ p U m hm)
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]

section SourceChange

variable {k l : ℕᵒᵖ}
variable [HasDerivedCategory.{wK}
  (Under k ⥤ Sheaf
    ((Scheme.smallEtaleTopology
      (Functor.obj (cmGeometricSchemeTower D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q) U)).over
      ((cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid).obj.obj k))
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]
variable [HasDerivedCategory.{wL}
  (Under l ⥤ Sheaf
    ((Scheme.smallEtaleTopology
      (Functor.obj (cmGeometricSchemeTower D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q) U)).over
      ((cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid).obj.obj l))
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]
variable [HasDerivedCategory.{wM}
  (Under l ⥤ Sheaf
    ((Scheme.smallEtaleTopology
      (Functor.obj (cmGeometricSchemeTower D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q) U)).over
      ((cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid).obj.obj k))
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]

local notation "restrictedAt" i "," d => cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedObject
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid i d
local notation "scalarAt" i "," d => cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid i d
local notation "evaluationAt" i "," d => cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid i d
local notation "associatedIsoAt" i "," d => cmHarrisGeometricAssociatedCoefficientSourceDerivedObjectIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid i d
local notation "constantIsoAt" i "," d => cmHarrisGeometricConstantCoefficientSourceDerivedObjectIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid i d
local notation "restriction" f => cmHarrisGeometricCoefficientSourceRestriction
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f
local notation "reindex" f => cmHarrisGeometricCoefficientSourceReindex
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f
local notation "derivedRestriction" f => cmHarrisGeometricCoefficientSourceRestrictionDerivedFunctor
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f
local notation "derivedReindex" f => cmHarrisGeometricCoefficientSourceReindexDerivedFunctor
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f
local notation "ordinaryChange" f => cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f
local notation "associatedChange" f => cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f
local notation "constantChange" f => cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f

/-- The canonical exact-derived source change of the actual restricted quotient
source diagram, using the ordinary specific comparison in its middle. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedChangeIso
    (f : k ⟶ l) (d : ℤ) :
    (derivedRestriction f).obj (restrictedAt l, d) ≅
      (derivedReindex f).obj (restrictedAt k, d) :=
  ((restriction f).mapDerivedCategorySingleFunctor d).app (restrictedSource l) ≪≫
    (DerivedCategory.singleFunctor (mixedCategory k, l) d).mapIso (ordinaryChange f) ≪≫
      (((reindex f).mapDerivedCategorySingleFunctor d).app (restrictedSource k)).symm

local notation "restrictedChange" f "," d =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedChangeIso
    D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f d

omit [HasDerivedCategory.{wC} coefficientCategory] in
/-- Exact recovery of the original source change after the two canonical
single-degree comparisons. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedChangeIso_hom
    (f : k ⟶ l) (d : ℤ) :
    (restrictedChange f, d).hom =
      ((restriction f).mapDerivedCategorySingleFunctor d).hom.app (restrictedSource l) ≫
        (DerivedCategory.singleFunctor (mixedCategory k, l) d).map (ordinaryChange f).hom ≫
        ((reindex f).mapDerivedCategorySingleFunctor d).inv.app (restrictedSource k) := rfl

omit [HasDerivedCategory.{wC} coefficientCategory] in
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedChangeIso_inv
    (f : k ⟶ l) (d : ℤ) :
    (restrictedChange f, d).inv =
      ((reindex f).mapDerivedCategorySingleFunctor d).hom.app (restrictedSource k) ≫
        (DerivedCategory.singleFunctor (mixedCategory k, l) d).map (ordinaryChange f).inv ≫
        ((restriction f).mapDerivedCategorySingleFunctor d).inv.app (restrictedSource l) := by
  simp only [cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedChangeIso,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc]

set_option maxHeartbeats 300000 in
/-- The complete derived scalar comparison commutes with source change of the
actual quotient system, with the original reductions retained. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_sourceChange
    (f : k ⟶ l) (d : ℤ) :
    (derivedRestriction f).map (scalarAt l, d).hom ≫
        (associatedChange f).hom.app (derivedCoefficient d) =
      (restrictedChange f, d).hom ≫
        (derivedReindex f).map (scalarAt k, d).hom := by
  exact exactSingleComparison_square
    (associatedSourceFunctor l) (associatedSourceFunctor k)
    (restriction f) (reindex f)
    (etaleAssociatedSourceChangeFunctorIso X covers coverProperty f)
    coefficients (sourceComparison l) (sourceComparison k) (ordinaryChange f)
    (cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_sourceChange
      D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f) d

/-- The scalar-restricted derived invariant evaluation commutes with the exact
geometric source change and the existing constant derived comparison. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_sourceChange
    (f : k ⟶ l) (d : ℤ) :
    (derivedRestriction f).map (evaluationAt l, d).hom ≫
        (constantChange f).hom.app (derivedCoefficient d) =
      (restrictedChange f, d).hom ≫
        (derivedReindex f).map (evaluationAt k, d).hom := by
  dsimp only [cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization,
    Iso.trans_hom, Iso.app_hom]
  exact comparisonSquare_comp (derivedRestriction f) (derivedReindex f)
    (scalarAt l, d).hom (scalarAt k, d).hom
    ((cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization
      D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid l).hom.app (derivedCoefficient d))
    ((cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization
      D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k).hom.app (derivedCoefficient d))
    (restrictedChange f, d).hom
    ((associatedChange f).hom.app (derivedCoefficient d))
    ((constantChange f).hom.app (derivedCoefficient d))
    (cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_sourceChange
      D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f d)
    (cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_sourceChange_app
      D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f (derivedCoefficient d))


end SourceChange

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
