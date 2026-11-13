import Langlands.Shimura.PEL.HarrisTaylorCMLocalPrimeComparison
import Langlands.AbelianScheme.Tate.RationalPrimeHom

/-! # The actual prime Tate operator of a fixed Harris self-isogeny -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
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
  {S : Scheme.{0}}
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

variable
  (X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

omit hμfin hμet in
/-- The actual prime Tate operator of a rational action-object self-isogeny. -/
def selfIsoPrimeTateOperator (v : Global.FinitePlace ℚ) :
    letI := auxiliaryStarRing D C
    (X.actionObj ≅ X.actionObj) →
    Module.End ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]
      (PrimeAdic.Rational X.actionObj.abelianScheme (Over.mk s)
        (Rat.HeightOneSpectrum.primesEquiv v).val) := by
  let := auxiliaryStarRing D C
  intro e
  exact PrimeAdic.rationalHomMap (Over.mk s) (Rat.HeightOneSpectrum.primesEquiv v).val
    (RationalAlgebraAction.hom0 e.hom)

/-- A fixed small-level orbit gives the identity actual prime Tate operator,
conditional on finite order of the actual rational self-isogeny. -/
theorem selfIsoPrimeTateOperator_eq_id_of_levelIso_fixed
    (U : HarrisLevel D) (v : Global.FinitePlace ℚ)
    (hsmall : D.rationalInvolution.LevelSmallAt U v) :
    letI := auxiliaryStarRing D C
    ∀ (a : (PolarizedWeilLevel.levelTower preservation composition unitCoherence
          associativity comparison symmetry stability square universality compatibility
          h A (D.harrisHodgePELForm C) s hs htor hu X).obj
            ((hodgeLevelFunctor D C).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj)
      (he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality additivity X X q e),
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) s hs htor hu additivity X X
        ((hodgeLevelFunctor D C).obj U) q e he a = a →
      (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
       IsOfFinOrder f) →
      selfIsoPrimeTateOperator D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality s X v e = LinearMap.id := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed hfin
  apply PrimeComparison.rationalHomMap_eq_id_of_extraction_fixed
    (Over.mk s) (Rat.HeightOneSpectrum.primesEquiv v).val
    X.actionObj.abelianScheme (RationalAlgebraAction.hom0 e.hom)
  exact rationalFullToPrime_fixed_of_levelIso_fixed D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s hs htor hu additivity X U v hsmall a q e he hfixed hfin

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
