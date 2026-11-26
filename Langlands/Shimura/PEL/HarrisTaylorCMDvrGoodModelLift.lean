import Langlands.Shimura.PEL.HarrisTaylorCMMultipleClassReduction
import Langlands.Shimura.PEL.HarrisTaylorCMDvrPolarizedAction
import Langlands.Shimura.PEL.HarrisTaylorCMDvrNormalization
import Langlands.Shimura.PEL.HarrisTaylorCMDvrGenericTransport
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof

/-! # Normalized positive polarized actions over a DVR from a good model -/

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
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Pos" base => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := base)

omit [IsCMField F] in
/-- The normalized determinant and dimension condition is invariant under an actual
equivariant rational isomorphism. -/
theorem harrisTaylorCMDeterminantDimensionCondition_of_iso {S : Scheme.{0}}
    (p : S ⟶ Spec (.of F)) {X Y : RationalAlgebraAction S A} (e : X ≅ Y)
    (hY : D.HarrisTaylorCMDeterminantDimensionCondition C p Y.abelianScheme Y.action) :
    D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action := by
  have hclass : RationalAlgebraAction.classOf X = RationalAlgebraAction.classOf Y :=
    RationalAlgebraAction.classOf_eq_iff.mpr ⟨e⟩
  refine ⟨?_, ?_⟩
  · have hdet := (D.harrisTaylorCMDeterminantClassCondition_classOf C p Y).mpr hY.1
    rw [← hclass] at hdet
    exact (D.harrisTaylorCMDeterminantClassCondition_classOf C p X).mp hdet
  · exact (rationalIsoRelativeDimension _ _ _ (RationalAlgebraAction.underlyingIso e) _).mpr hY.2

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]

local notation "j" => Spec.algebraMap V K

/-- The named prerequisites, with the published dual base-change theorem and the
given polarization base-change statement. -/
abbrev dvrLiftPrerequisites : Prerequisites.{0} :=
  ⟨preservation, square, universality, stability, composition, unitCoherence, associativity,
    comparison, symmetry, dualAbelianBaseChange, polarizationStability⟩

/-- A constructed dual witness for an abelian scheme over a quasi-separated base. -/
def constructedDualWitness {S : Scheme.{0}} [QuasiSeparatedSpace S] (G : AbelianScheme S) :
    DualWitness G :=
  let W := dualEvaluationDataOfGeometry preservation stability G
    (relativeDualSchemeExistence _ G) (relativeDualSchemeGeometry _ G _)
  ⟨W.hasDual, W.geometry, W.inversePoincare, W.evaluation⟩

include dualityNaturality polarizationStability in
set_option maxHeartbeats 4000000 in
/-- A good abelian model over a DVR of the abelian variety of a normalized
positive polarized action over its fraction field carries a normalized positive
polarized action whose restriction is the given one, with polarization
multiplier one half. -/
theorem dvrNormalizedLift_of_goodModel (β : Spec (.of V) ⟶ Spec (.of F))
    (X : Pos (Spec (.of K)))
    (hGood : PositiveObjectCondition D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C (j ≫ β)) X)
    (hNum : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L (j ≫ β) X)
    (G : AbelianScheme (Spec (.of V)))
    (e₀ : letI := auxiliaryStarRing D C
      (baseChange j).obj G ≅ X.actionObj.abelianScheme) :
    letI := auxiliaryStarRing D C
    ∃ Y : Pos (Spec (.of V)),
      PositiveObjectCondition D C hΦ preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C β) Y ∧
      HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality L β Y ∧
      ∃ (q : ℚˣ) (e : (RationalAlgebraAction.pullback j).obj Y.actionObj ≅ X.actionObj),
        PositivePolarizedActionReductionMultiple D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality j Y X q e := by
  let := auxiliaryStarRing D C
  let P := dvrLiftPrerequisites preservation composition unitCoherence associativity comparison
    symmetry stability square universality polarizationStability
  let GK := (baseChange j).obj G
  let WG := constructedDualWitness preservation stability G
  let WGK := WG.pullback P j
  let X' := transportDvrGenericPolarizedAction P X GK WGK e₀
  let addS := relativeDualSchemeMapAdditivity preservation stability _ G G WG.hasDual WG.hasDual
  let addK := relativeDualSchemeMapAdditivity preservation stability _ GK GK
    WGK.hasDual WGK.hasDual
  let Y : Pos (Spec (.of V)) := extendDvrPolarizedAction K P dualityNaturality G WG addS addK
    X'.actionObj.action X'.faithful X'.polarization X'.isPolarization X'.involutionCompatible
  have hi₀ : (rationalBaseChangeEnd j G).comp Y.actionObj.action = X'.actionObj.action :=
    rationalBaseChangeEnd_extendDvrRationalAction (V := V) (A := A) K G X'.actionObj.action
  let e₁ : (RationalAlgebraAction.pullback j).obj Y.actionObj ≅ X'.actionObj :=
    RationalAlgebraAction.isoMk (Iso.refl _) (fun d => by
      change comp0 GK GK GK (((rationalBaseChangeEnd j G).comp Y.actionObj.action) d).asHom
          (id0 GK) = comp0 GK GK GK (id0 GK) (X'.actionObj.action d).asHom
      rw [hi₀, comp0_id0, id0_comp0]
      rfl)
  let e₂ := transportDvrGenericActionIso P X GK WGK e₀
  refine ⟨Y, ?_, ?_, Units.mk0 (2⁻¹ : ℚ) (by norm_num), e₁ ≪≫ e₂, ?_⟩
  rotate_right
  · -- the multiplier equation for every constrained choice of dual data
    intro W'
    let lam₀ : G ⟶ WG.dual P := Y.polarization
    let lamGK := WG.pullbackMap P j WGK lam₀
    let lamW' := dualAbelianBaseChangeMap preservation stability composition unitCoherence
      associativity comparison symmetry universality dualAbelianBaseChange j G
      WG.hasDual WG.geometry WG.inverseBundle WG.evaluation
      W'.hasDual W'.geometry W'.inversePoincare W'.evaluation lam₀
    have h0 := IsRationalDualPullbackMultiple.id preservation composition unitCoherence
      associativity comparison symmetry stability WG.hasDual WG.geometry WG.inverseBundle
      WG.evaluation addS (homToHom0 lam₀)
    have h0' := IsRationalDualPullbackMultiple.integral_baseChange_of_naturality preservation
      stability composition unitCoherence associativity comparison symmetry universality
      dualAbelianBaseChange j G G WG.hasDual WG.geometry WG.inverseBundle WG.evaluation
      WG.hasDual WG.geometry WG.inverseBundle WG.evaluation
      W'.hasDual W'.geometry W'.inversePoincare W'.evaluation
      WGK.hasDual WGK.geometry WGK.inverseBundle WGK.evaluation addS
      (relativeDualSchemeMapAdditivity preservation stability _ GK GK W'.hasDual WGK.hasDual)
      dualityNaturality 1 (id0 G) lam₀ lam₀ h0
    have hdouble : lamGK = 2 • X'.polarization :=
      pullbackMap_extendDvrPolarizationDouble (V := V) K P G WG X'.polarization X'.isPolarization
    have h1 : IsRationalDualPullbackMultiple preservation composition unitCoherence
        associativity comparison symmetry stability WGK.hasDual X.hasDual WGK.geometry
        X.geometry WGK.inverseBundle WGK.evaluation X.inversePoincare X.evaluation
        (relativeDualSchemeMapAdditivity preservation stability _ GK _ WGK.hasDual X.hasDual)
        (2⁻¹ : ℚ) (homToHom0 e₀.hom) (homToHom0 lamGK)
        (homToHom0 X.polarization) := by
      change rationalDualPullbackHom0 preservation composition unitCoherence associativity
        comparison symmetry stability WGK.hasDual X.hasDual WGK.geometry X.geometry
        WGK.inverseBundle WGK.evaluation X.inversePoincare X.evaluation
        (relativeDualSchemeMapAdditivity preservation stability _ GK _ WGK.hasDual X.hasDual)
        (homToHom0 e₀.hom) (homToHom0 X.polarization) = (2⁻¹ : ℚ) • homToHom0 lamGK
      rw [← homToHom0_transportDvrGenericPolarization P X GK WGK e₀, hdouble, map_nsmul,
        ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      norm_num
      rfl
    have h2 := IsRationalDualPullbackMultiple.comp preservation composition unitCoherence
      associativity comparison symmetry stability W'.hasDual WGK.hasDual W'.geometry
      WGK.geometry W'.inversePoincare W'.evaluation WGK.inverseBundle WGK.evaluation
      (relativeDualSchemeMapAdditivity preservation stability _ GK GK W'.hasDual WGK.hasDual)
      X.hasDual X.geometry X.inversePoincare X.evaluation
      (relativeDualSchemeMapAdditivity preservation stability _ GK _ WGK.hasDual X.hasDual)
      (relativeDualSchemeMapAdditivity preservation stability _ GK _ W'.hasDual X.hasDual)
      1 (2⁻¹ : ℚ) (rationalBaseChangeHom j (id0 G)) (homToHom0 e₀.hom)
      (homToHom0 lamW') (homToHom0 lamGK) (homToHom0 X.polarization) h0' h1
    have hid : rationalBaseChangeHom j (id0 G) = id0 GK := rationalBaseChangeHom_identity j G
    have hq : ((Units.mk0 (2⁻¹ : ℚ) (by norm_num) : ℚˣ) : ℚ) = 1 * 2⁻¹ := by simp
    have hf : (RationalAlgebraAction.underlyingIso (e₁ ≪≫ e₂)).hom =
        comp0 GK GK X.actionObj.abelianScheme (rationalBaseChangeHom j (id0 G))
          (homToHom0 e₀.hom) := by
      rw [hid]
      rfl
    intro lam
    rw [hq, hf]
    exact h2
  all_goals
    have hX := (determinantDimensionCondition_iff D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (j ≫ β) X).mpr
      ⟨hGood, hNum⟩
    have hX' := harrisTaylorCMDeterminantDimensionCondition_of_iso D C (j ≫ β) e₂ hX
    have hYK : D.HarrisTaylorCMDeterminantDimensionCondition C (j ≫ β) GK
        ((rationalBaseChangeEnd j G).comp Y.actionObj.action) := by
      rw [hi₀]
      exact hX'
    have hY := D.harrisTaylorCMDvrNormalization C (V := V) K β G Y.actionObj.action hYK
    have hYY := (determinantDimensionCondition_iff D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality β Y).mp hY
  · exact hYY.1
  · exact hYY.2

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
