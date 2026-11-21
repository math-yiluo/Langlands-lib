import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedClasses
import Langlands.Shimura.Unitary.DivisionCondition
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Artinian lifting of the actual positive polarized action -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

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

local notation "Pos" base => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := base)

/-- Compare an actual positive polarized action with the reduction of another one
by an equivariant rational isometry of their polarizations, using the actual
base change of the thicker polarization. -/
def PositivePolarizedActionIsometricReduction
    {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
    (b : T ⟶ S) (X : Pos S) (Y : Pos T) :
    letI := auxiliaryStarRing D C
    ((RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj) → Prop :=
  letI := auxiliaryStarRing D C
  fun e => ∀ W : PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality b X,
    let lam := dualAbelianBaseChangeMap preservation stability composition unitCoherence
      associativity comparison symmetry universality dualAbelianBaseChange b
      X.actionObj.abelianScheme X.hasDual X.geometry X.inversePoincare X.evaluation
      W.hasDual W.geometry W.inversePoincare W.evaluation X.polarization
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability W.hasDual Y.hasDual W.geometry Y.geometry
      W.inversePoincare W.evaluation Y.inversePoincare Y.evaluation
      (relativeDualSchemeMapAdditivity preservation stability T _ _ W.hasDual Y.hasDual)
      1 (RationalAlgebraAction.underlyingIso e).hom
      (Rationalization.ofHom lam) (Rationalization.ofHom Y.polarization)

/-- Level-free geometric lifting for the normalized positive polarized actions
occurring in the division-case Artinian tests. -/
def DivisionCMPolarizedActionArtinianLiftingStatement : Prop :=
  letI := auxiliaryStarRing D C
  D.IsDivision →
    ∀ (R' R : Type) [CommRing R'] [CommRing R] [IsLocalRing R'] [IsLocalRing R]
      [IsArtinianRing R'] [IsArtinianRing R] (φ : R' →+* R), Function.Surjective φ →
      maximalIdeal R' * RingHom.ker φ = ⊥ →
      ∀ β : Spec (.of R') ⟶ Spec (.of F),
        let b := Spec.map (CommRingCat.ofHom φ)
        ∀ Y : Pos (Spec (.of R)),
          D.HarrisTaylorCMDeterminantDimensionCondition C (b ≫ β)
            Y.actionObj.abelianScheme Y.actionObj.action →
          ∃ X : Pos (Spec (.of R')),
            ∃ e : (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj,
              PositivePolarizedActionIsometricReduction D C preservation composition
                unitCoherence associativity comparison symmetry stability square universality
                b X Y e

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
