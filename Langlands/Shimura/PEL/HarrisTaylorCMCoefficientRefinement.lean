import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSheaf

/-! # Original CM coefficient sheaves under normal cover refinement -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients

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

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

variable (hRigid : CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor U.obj)

variable
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0) (k : ℕ)

local notation "X" => Functor.obj (schemes q) U
local notation "Vcoeff" => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "Rcoeff" => HarrisCoefficientReductionRing K p m k
local notation "Mcoeff" => cmHarrisCoefficientAction D ρ p U m hm k
local notation "J" => Scheme.smallEtaleTopology X

variable (V : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (hV : V.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
include hm hV in
/-- Kernel containment follows from inclusion in the constructed full kernel level. -/
theorem cmHarrisRefinement_kernel_le :
    V.obj.subgroup.subgroupOf U.obj.subgroup ≤ cmHarrisCongruenceKernel D ρ p U m k := by
  rw [← cmHarrisCoefficientLevel_subgroupOf D ρ p U m hm k]
  exact fun _ hx => hV hx

local notation "hVU" => hV.trans (cmHarrisCoefficientLevel_le D ρ p U m hm k)
local notation "φ" => smallCMResidualQuotientMap D U Vcoeff V hV
local notation "fineAction" => cmHarrisResidualCoefficientAction D ρ p U V m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k V hV)

/-- Restricting the canonical action gives the independently factored fine-level action. -/
def cmHarrisCoefficientRefinementActionIso :
    (Action.res (ModuleCat.{0} Rcoeff) φ).obj Mcoeff ≅ fineAction :=
  Action.mkIso (Iso.refl _) (by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (cmHarrisFiniteTorsionAction D ρ p U m k).ρ g ≫ 𝟙 _ =
        𝟙 _ ≫ (cmHarrisFiniteTorsionAction D ρ p U m k).ρ g
      simp only [Category.comp_id, Category.id_comp])

@[simp] theorem cmHarrisCoefficientRefinementActionIso_hom_hom :
    (cmHarrisCoefficientRefinementActionIso D U ρ p m hm k V hV).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisCoefficientRefinementActionIso_inv_hom :
    (cmHarrisCoefficientRefinementActionIso D U ρ p m hm k V hV).inv.hom = 𝟙 _ := rfl

local notation "Y" => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

/-- The original normal fine cover, with its geometric torsor property derived. -/
def cmHarrisRefinementTorsor :
    {Z : Action (X).Etale (SmallCMResidualGroup D U V) // IsFiniteGeometricTorsor X Z} :=
  cmNormalGeometricTorsor_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor U V hVU q
    existence geometry hRigid DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "Z" => cmHarrisRefinementTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

@[simp] theorem cmHarrisRefinementTorsor_left :
    (Z).val.V.left = (schemes q).obj V := rfl

@[simp] theorem cmHarrisRefinementTorsor_hom :
    (Z).val.V.hom = (schemes q).map (smallCMInclusion D hVU) := rfl

@[simp] theorem cmHarrisRefinementTorsor_ρ_left (g : SmallCMResidualGroup D U V) :
    ((Z).val.ρ g).left =
      (cmNormalQuotientAction D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q).ρ g := rfl

/-- Original scheme forgetting, as an equivariant map in the actual small etale site. -/
def cmHarrisCoefficientRefinementCover :
    (Z).val ⟶ (Action.res (X).Etale φ).obj (Y).val where
  hom := MorphismProperty.Over.homMk ((schemes q).map (smallCMInclusion D hV)) (by
    change (schemes q).map (smallCMInclusion D hV) ≫
        (schemes q).map (smallCMInclusion D (cmHarrisCoefficientLevel_le D ρ p U m hm k)) =
      (schemes q).map (smallCMInclusion D hVU)
    rw [← (schemes q).map_comp, smallCMInclusion_trans])
  comm g := by
    apply MorphismProperty.Over.Hom.ext
    exact (cmNormalRefinement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U Vcoeff V
      (cmHarrisCoefficientLevel_le D ρ p U m hm k) hV q).comm g

local notation "a" => cmHarrisCoefficientRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

@[simp] theorem cmHarrisCoefficientRefinementCover_left :
    (a).hom.left = (schemes q).map (smallCMInclusion D hV) := rfl

/-- The fine cover covers the terminal object of the original coarse small-etale site. -/
theorem cmHarrisRefinementTorsor_coversTop :
    (J).CoversTop (fun _ : Unit => (Z).val.V) :=
  etale_coversTop_of_surjective (Z).val.V (Z).property.2.2.1


local notation "reps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The cover refinement preserves the structure over the original CM field. -/
@[reassoc] theorem cmHarrisCoefficientRefinementCover_over :
    (a).hom.left ≫ ((reps) Vcoeff).base.obj.hom = ((reps) V).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor reps (smallCMInclusion D hV)

/-- The coefficient sheaf formed from the independently factored action on the finer cover. -/
def cmHarrisRefinementCoefficientSheaf : Sheaf J (ModuleCat.{0} Rcoeff) :=
  (etaleAssociatedFunctor X (Z).val).obj fineAction

local notation "fineSheaf" => cmHarrisRefinementCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
set_option quotPrecheck false in
local notation "constantFineAction" =>
  Functor.obj (Functor.mapAction (constantSheaf J (ModuleCat.{0} Rcoeff))
    (SmallCMResidualGroup D U V)) fineAction
set_option quotPrecheck false in
local notation "constantAction" =>
  Functor.obj (Functor.mapAction (constantSheaf J (ModuleCat.{0} Rcoeff))
    (SmallCMResidualGroup D U Vcoeff)) Mcoeff
set_option quotPrecheck false in
local notation "constantModule" => (constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V

/-- Invariant inclusion for the independent fine-cover construction. -/
def cmHarrisRefinementCoefficientInclusion :
    fineSheaf ⟶ (productSheaf J (Z).val.V).obj constantModule :=
  inclusion J (Z).val constantFineAction

local notation "fineInclusion" => cmHarrisRefinementCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "coarseSheaf" => cmHarrisCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "coarseInclusion" => cmHarrisCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "actionIso" => cmHarrisCoefficientRefinementActionIso D U ρ p m hm k V hV

/-- Fine-cover sections satisfy the original inverse-deck diagonal invariance. -/
@[reassoc] theorem cmHarrisRefinementCoefficientInclusion_invariant
    (g : SmallCMResidualGroup D U V) :
    fineInclusion ≫ (diagonal J (Z).val constantFineAction).ρ g = fineInclusion :=
  inclusion_invariant J (Z).val constantFineAction g

/-- Normal cover refinement does not change the original associated coefficient sheaf. -/
def cmHarrisCoefficientRefinementIso : coarseSheaf ≅ fineSheaf := by
  let e := etaleCrossCoverMap X φ a
    (𝟙 ((Action.res (ModuleCat.{0} Rcoeff) φ).obj Mcoeff))
  haveI : IsIso e := etaleAssociatedCoverComparison X _ _ (Y).val (Z).val
    (Y).property (Z).property φ a Rcoeff Mcoeff
  exact asIso e ≪≫ (etaleAssociatedFunctor X (Z).val).mapIso actionIso

local notation "refinementIso" => cmHarrisCoefficientRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

/-- The sheaf comparison restricts the original cover coordinate along actual forgetting. -/
@[reassoc] theorem cmHarrisCoefficientRefinementIso_hom_inclusion :
    (refinementIso).hom ≫ fineInclusion =
      coarseInclusion ≫ coverPullback J (a).hom constantModule := by
  let c₀ := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U V)).map
      (𝟙 ((Action.res (ModuleCat.{0} Rcoeff) φ).obj Mcoeff))
  let c₁ := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U V)).map (actionIso).hom
  have hc₀ : c₀.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} Rcoeff)).map (𝟙 (Mcoeff).V) = _
    exact (constantSheaf J (ModuleCat.{0} Rcoeff)).map_id _
  have hc₁ : c₁.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} Rcoeff)).map (𝟙 (Mcoeff).V) = _
    exact (constantSheaf J (ModuleCat.{0} Rcoeff)).map_id _
  have hid : (productSheaf J (Z).val.V).map (𝟙 constantModule) = 𝟙 _ :=
    (productSheaf J (Z).val.V).map_id constantModule
  have hn := inclusion_natural J (Z).val c₁
  erw [hc₁, hid] at hn
  have hn' := hn.trans (Category.comp_id _)
  have he := crossCoverMap_inclusion (R := Rcoeff) J φ a
    (F := constantAction)
    (E := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
      (SmallCMResidualGroup D U V)).obj
        ((Action.res (ModuleCat.{0} Rcoeff) φ).obj Mcoeff)) c₀
  erw [hc₀, hid] at he
  have he' := he.trans (congrArg (fun b => inclusion J (Y).val constantAction ≫ b)
    (Category.comp_id (coverPullback J (a).hom constantModule)))
  change (crossCoverMap J φ a (F := constantAction) c₀ ≫
    (associatedFunctor J (Z).val).map c₁) ≫
    inclusion J (Z).val constantFineAction = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun b =>
    crossCoverMap J φ a (F := constantAction) c₀ ≫ b) hn').trans he')

/-- The forward isomorphism is exactly the original cross-cover map with identity coefficients. -/
theorem cmHarrisCoefficientRefinementIso_hom :
    (refinementIso).hom = etaleCrossCoverMap X φ a (actionIso).hom := by
  let c := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U V)).map (actionIso).hom
  have hc : c.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} Rcoeff)).map (𝟙 (Mcoeff).V) = _
    exact (constantSheaf J (ModuleCat.{0} Rcoeff)).map_id _
  have he := crossCoverMap_inclusion (R := Rcoeff) J φ a
    (F := constantAction) (E := constantFineAction) c
  have hid : (productSheaf J (Z).val.V).map (𝟙 constantModule) = 𝟙 _ :=
    (productSheaf J (Z).val.V).map_id constantModule
  erw [hc, hid, Category.comp_id] at he
  apply Langlands.Shimura.Coefficients.hom_ext J (Z).val
  exact (cmHarrisCoefficientRefinementIso_hom_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V hV).trans he.symm

/-- The inverse comparison is normalized by the same original restriction of cover sections. -/
@[reassoc] theorem cmHarrisCoefficientRefinementIso_inv_inclusion :
    (refinementIso).inv ≫ coarseInclusion ≫ coverPullback J (a).hom constantModule =
      fineInclusion := by
  rw [← cmHarrisCoefficientRefinementIso_hom_inclusion]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Canonical evaluation on the independently constructed fine cover. -/
def cmHarrisRefinementCoefficientTrivialization :
    ((J).overPullback (ModuleCat.{0} Rcoeff) (Z).val.V).obj fineSheaf ≅
      ((J).overPullback (ModuleCat.{0} Rcoeff) (Z).val.V).obj constantModule :=
  (constantAssociatedTrivializationOfSplitting J (Z).val
    (etaleTorsorSectionSplitting X _ (Z).val (Z).property Rcoeff)).app fineAction

local notation "fineTrivialization" => cmHarrisRefinementCoefficientTrivialization
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k V hV

/-- Refinement intertwines fine evaluation with original coefficient-cover evaluation along forgetting. -/
@[reassoc] theorem cmHarrisCoefficientRefinementIso_evaluation :
    ((J).overPullback (ModuleCat.{0} Rcoeff) (Z).val.V).map (refinementIso).hom ≫
        (fineTrivialization).hom =
      associatedEvaluationAlong J (Y).val (a).hom constantAction := by
  let c := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U V)).map (actionIso).hom
  have hc : c.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} Rcoeff)).map (𝟙 (Mcoeff).V) = _
    exact (constantSheaf J (ModuleCat.{0} Rcoeff)).map_id _
  have he := crossCoverMap_evaluation (R := Rcoeff) J φ a
    (F := constantAction) (E := constantFineAction) c
  have hid :
      ((J).overPullback (ModuleCat.{0} Rcoeff) (Z).val.V).map (𝟙 constantModule) = 𝟙 _ :=
    ((J).overPullback (ModuleCat.{0} Rcoeff) (Z).val.V).map_id constantModule
  erw [hc, hid, Category.comp_id] at he
  rw [cmHarrisCoefficientRefinementIso_hom]
  exact he

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
