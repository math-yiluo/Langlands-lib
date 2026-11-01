import Langlands.Shimura.PEL.HarrisIntegralRosatiLocus
import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantGlobal

/-! # The joint integral Harris Rosati and normalized determinant locus -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme.Cartier

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))

variable
    (preservation : pullbackTensorComparisonIsIsoStatement.{0})
    (composition : PullbackTensorCompositionStatement.{0})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
    (symmetry : PullbackTensorSymmetryStatement.{0})
    (stability : PicardZeroPullbackStatement.{0})
    {S : Scheme.{0}} [IsLocallyNoetherian S] (p : S ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme S)
    (hB : HasDualScheme B)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (geometryB : DualSchemeGeometry B hB)

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualInt" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "tauO" => D.harrisHodgePELIntegralInvolution C

variable (H : Over S)
    (e : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme
          (dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
            evaluationB stability composition unitCoherence associativity comparison
            symmetry).toCommGroupScheme ⋙ forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj H)
    (a : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End B)
    (lam : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
      evaluationB stability composition unitCoherence associativity comparison symmetry)


local notation "R" => integralRosatiLocus D C preservation composition unitCoherence
  associativity comparison symmetry stability B hB MB evaluationB geometryB H e a lam
local notation "iA" => D.harrisHodgePELRationalAction C B a
local notation "Zdet" => D.harrisTaylorCMGlobalDeterminantLocus C p B iA
local notation "detι" => D.harrisTaylorCMGlobalDeterminantLocusι C p B iA

/-- The actual intersection of the integral Rosati and normalized rational determinant loci. -/
def integralCMEquationLocus : Scheme.{0} := pullback (R).hom detι

/-- The joint equation locus maps to the supplied integral-action family base. -/
def integralCMEquationLocusι :
    integralCMEquationLocus D C preservation composition unitCoherence associativity
      comparison symmetry stability p B hB MB evaluationB geometryB H e a lam ⟶ S :=
  pullback.fst (R).hom detι ≫ (R).hom

local notation "Z" => integralCMEquationLocus D C preservation composition unitCoherence
  associativity comparison symmetry stability p B hB MB evaluationB geometryB H e a lam
local notation "ι" => integralCMEquationLocusι D C preservation composition unitCoherence
  associativity comparison symmetry stability p B hB MB evaluationB geometryB H e a lam

instance integralCMEquationLocusι_isClosedImmersion [IsSeparated H.hom] :
    IsClosedImmersion ι := by
  unfold integralCMEquationLocusι
  infer_instance

instance integralCMEquationLocus_isLocallyNoetherian [IsSeparated H.hom] :
    IsLocallyNoetherian Z :=
  LocallyOfFiniteType.isLocallyNoetherian ι

section Test

variable
    (universality : PicardZeroUniversalBaseChangeStatement.{0})
    (compatibility : DualAbelianBaseChangeStatement.{0})
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (hT : HasDualScheme ((baseChange T.obj.hom).obj B))
    (MT : LineBundle ((relativeSpace ((baseChange T.obj.hom).obj B).X.hom).obj
      (dualScheme ((baseChange T.obj.hom).obj B) hT)))
    (evaluationT : tensorObj (poincareFamily ((baseChange T.obj.hom).obj B) hT).obj.carrier
      MT.obj ≅ structureSheaf ((relativeSpace ((baseChange T.obj.hom).obj B).X.hom).obj
        (dualScheme ((baseChange T.obj.hom).obj B) hT)))
    (geometryT : DualSchemeGeometry ((baseChange T.obj.hom).obj B) hT)

local notation "pullLam" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T.obj.hom B
  hB geometryB MB evaluationB hT geometryT MT evaluationT
local notation "aT" => baseChangeOrderAction T.obj.hom B a
local notation "BT" => Functor.obj (baseChange T.obj.hom) B
local notation "rosatiT" => IntegralRosatiBasisEquations D C preservation composition
  unitCoherence associativity comparison symmetry stability BT hT MT evaluationT geometryT
  aT (pullLam lam)
local notation "detT" => D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p)
  BT (D.harrisHodgePELRationalAction C BT aT)

/-- A test map factors through the intersection exactly when both actual conditions hold. -/
theorem integralCMEquationLocus_factors_iff_basis :
    (∃ k : T.obj.left ⟶ Z, k ≫ ι = T.obj.hom) ↔ rosatiT ∧ detT := by
  have hdet : (∃ d : T.obj.left ⟶ Zdet, d ≫ detι = T.obj.hom) ↔ detT := by
    rw [D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B iA T.obj.hom]
    rw [D.harrisHodgePELRationalAction_baseChange]
  have hrosati := integralRosatiLocus_nonempty_iff_basis D C preservation composition
    unitCoherence associativity comparison symmetry stability B hB MB evaluationB
    geometryB H e a lam universality compatibility T hT MT evaluationT geometryT
  constructor
  · rintro ⟨k, hk⟩
    have hr : Nonempty (T.obj ⟶ R) :=
      ⟨Over.homMk (k ≫ pullback.fst (R).hom detι) (by
        simpa only [integralCMEquationLocusι, Category.assoc] using hk)⟩
    refine ⟨hrosati.mp hr, hdet.mp ⟨k ≫ pullback.snd (R).hom detι, ?_⟩⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hk
  · rintro ⟨hr, hd⟩
    obtain ⟨r⟩ := hrosati.mpr hr
    obtain ⟨d, hd⟩ := hdet.mpr hd
    refine ⟨pullback.lift r.left d ((Over.w r).trans hd.symm), ?_⟩
    change pullback.lift r.left d _ ≫ (pullback.fst (R).hom detι ≫ (R).hom) = _
    rw [← Category.assoc, pullback.lift_fst]
    exact Over.w r

/-- Closedness gives a unique actual lift for precisely the simultaneous conditions. -/
theorem integralCMEquationLocus_unique_factors_iff_basis [IsSeparated H.hom] :
    (∃! k : T.obj.left ⟶ Z, k ≫ ι = T.obj.hom) ↔ rosatiT ∧ detT := by
  constructor
  · intro hk
    exact (integralCMEquationLocus_factors_iff_basis D C preservation composition
      unitCoherence associativity comparison symmetry stability p B hB MB evaluationB
      geometryB H e a lam universality compatibility T hT MT evaluationT geometryT).mp hk.exists
  · intro h
    obtain ⟨k, hk⟩ := (integralCMEquationLocus_factors_iff_basis D C preservation composition
      unitCoherence associativity comparison symmetry stability p B hB MB evaluationB
      geometryB H e a lam universality compatibility T hT MT evaluationT geometryT).mpr h
    refine ⟨k, hk, ?_⟩
    intro k' hk'
    exact (cancel_mono ι).mp (hk'.trans hk.symm)

/-- With actual dual additivity, the joint locus imposes all integral Rosati equations. -/
theorem integralCMEquationLocus_factors_iff
    (additivityT : DualSchemeMapAdditivity preservation stability BT BT hT hT) :
    (∃ k : T.obj.left ⟶ Z, k ≫ ι = T.obj.hom) ↔
      IntegralRosatiEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability BT hT MT evaluationT geometryT aT (pullLam lam) ∧
      detT := by
  rw [integralRosatiEquations_iff_basis D C preservation composition unitCoherence
    associativity comparison symmetry stability BT hT additivityT MT evaluationT geometryT]
  exact integralCMEquationLocus_factors_iff_basis D C preservation composition
    unitCoherence associativity comparison symmetry stability p B hB MB evaluationB
    geometryB H e a lam universality compatibility T hT MT evaluationT geometryT

/-- Every factorization gives the published rational involution condition and determinant. -/
theorem integralCMEquationLocus_factors_involutionCompatible
    (additivityT : DualSchemeMapAdditivity preservation stability BT BT hT hT)
    (hk : ∃ k : T.obj.left ⟶ Z, k ≫ ι = T.obj.hom) :
    letI := auxiliaryStarRing D C
    IsInvolutionCompatible preservation composition unitCoherence associativity comparison
      symmetry stability hT additivityT MT evaluationT geometryT
      (D.harrisHodgePELRationalAction C BT aT).toRingHom (homToHom0 (pullLam lam)) ∧ detT := by
  let _ := auxiliaryStarRing D C
  have h := (integralCMEquationLocus_factors_iff_basis D C preservation composition
    unitCoherence associativity comparison symmetry stability p B hB MB evaluationB
    geometryB H e a lam universality compatibility T hT MT evaluationT geometryT).mp hk
  exact ⟨rationalAction_involutionCompatible_of_integralBasis D C preservation composition
    unitCoherence associativity comparison symmetry stability BT hT additivityT MT
    evaluationT geometryT aT (pullLam lam) h.1, h.2⟩

end Test

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
