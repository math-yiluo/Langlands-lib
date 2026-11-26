import Langlands.Shimura.PEL.HarrisTaylorCMDvrGoodModelLift
import Langlands.Shimura.PEL.HarrisTaylorCMDvrPointedReduction
import Langlands.Shimura.PEL.HarrisTaylorCMDvrMonodromy

/-! # Valuative extension of normalized Harris classes from good models -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry
open GroupScheme.Tate (Index)

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "connTest" => connectedSpecTest D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality

/-- Good models of level representatives: at the small level `U`, for every discrete
valuation ring `V` with fraction field `K`, every structure morphism `β` of `Spec V`
and every geometric point of `Spec K`, the abelian scheme of every normalized
representative over `Spec K` with a fixed level orbit at `U` is isomorphic to the
generic fibre of an abelian scheme over `Spec V`. -/
def CMLevelDvrGoodModelStatement (U : SmallCMLevel D) : Prop :=
  letI := auxiliaryStarRing D C
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (β : Spec (.of V) ⟶ Spec (.of F))
    (a : HarrisGeometricPoint (connTest K (Spec.algebraMap V K ≫ β)).obj.left)
    (x : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h a.hom a.finiteFibers htor
      (connTest K (Spec.algebraMap V K ≫ β)).property.torsionUnits U.obj),
    PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
        comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C (Spec.algebraMap V K ≫ β)) x.1 →
      HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality L
        (Spec.algebraMap V K ≫ β) x.1 →
      ∃ G : AbelianScheme (Spec (.of V)),
        Nonempty ((Langlands.AbelianScheme.baseChange (Spec.algebraMap V K)).obj G ≅
          x.1.actionObj.abelianScheme)

private theorem classTowerPresentationEq_surjective' (T : Bases)
    {q : T.obj.left ⟶ Spec (.of F)} (hq : q = T.obj.hom)
    (a : HarrisGeometricPoint T.obj.left) (U : HarrisLevel D) :
    Function.Surjective ((classTowerPresentationEq D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h htor T.property.torsionUnits T.property.pairAdditivity
      hq (rfl : a.hom = a.hom) a.finiteFibers a.finiteFibers).app U) := by
  subst q
  exact Function.surjective_id

/-- Good models of the level representatives give the existence part of the
valuative criterion for the normalized class presheaf at the small level `U`. -/
theorem cmLevelDiscreteValuativeExistence_of_goodModels (U : SmallCMLevel D)
    (hgood : CMLevelDvrGoodModelStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor U) :
    CMLevelDiscreteValuativeExistenceStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U := by
  let := auxiliaryStarRing D C
  intro V K _ _ _ _ _ _ β
  let j := Spec.algebraMap V K
  let Xc := connTest V β
  let Yc := connTest K (j ≫ β)
  let g : Yc ⟶ Xc := connectedSpecTestMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (algebraMap V K) β
  let a := Classical.arbitrary (HarrisGeometricPoint Yc.obj.left)
  refine (specTest_map_surjective_iff_pointed D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (algebraMap V K) β U a).mpr ?_
  let b := g.hom.left
  let aS := a.comp b
  let duals := unpointedPullbackDualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality g
  have hα := dvrGenericMonodromy_surjective V K a.hom a.finiteFibers aS.finiteFibers
  have hPoint := classBaseChange_surjective_of_levelMultipleLifts D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor b Xc.obj.hom a.hom
    a.finiteFibers aS.finiteFibers Xc.property.torsionUnits Yc.property.torsionUnits duals
    Xc.property.lieNaturality Xc.property.pairAdditivity Yc.property.pairAdditivity U.obj
    (fun x hx hnx => by
      obtain ⟨G, ⟨e₀⟩⟩ := hgood V K β a x hx hnx
      exact dvrNormalizedLift_of_goodModel D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability K β x.1 hx hnx G e₀) hα
  dsimp only [geometricFamilyPointPullback]
  rw [classTowerBaseChangeAlong_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor g.hom.left Xc.obj.hom Yc.obj.hom aS.hom a.hom
    (Over.w g.hom) rfl aS.finiteFibers a.finiteFibers Xc.property.lieNaturality
    Xc.property.torsionUnits Yc.property.torsionUnits duals Xc.property.pairAdditivity
    Yc.property.pairAdditivity aS.finiteFibers]
  simp only [classTowerPresentationEq_refl, Category.id_comp, NatTrans.comp_app]
  exact (classTowerPresentationEq_surjective' D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor
    Yc (Over.w g.hom) a U.obj).comp hPoint

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
