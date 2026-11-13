import Langlands.Shimura.PEL.HarrisTaylorCMPrimeOperator
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelRigidityStatement

/-! # A conditional reduction of exact CM small-level rigidity -/

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

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
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


variable {S : Scheme.{0}}
  (p : S ⟶ Spec (.of F))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexStructure" => D.harrisTaylorReflexStructure C p
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
local notation "Num" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "orbitTower" => PolarizedWeilLevel.levelTower preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu
local notation "transport" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity

/-- Actual finite order of the underlying rational endomorphism of every
fixed coarse-level self-isogeny passing the original object tests. -/
def CMCoarseLevelFiniteOrder (U : HarrisLevel D) : Prop :=
  letI := auxiliaryStarRing D C
  ∀ (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)),
    Good X → Num X →
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj)
      (he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality additivity X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
        (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
         IsOfFinOrder f)

/-- The coarse finite-order condition at every admitted algebraically closed
field spectrum, using the actual identity geometric point. -/
def CMGeometricCoarseFiniteOrder (U : HarrisLevel D) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (hp : AdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p)),
    letI : ∀ k : GroupScheme.Tate.Index (fun _ => True),
        IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muFinite
    letI : ∀ k : GroupScheme.Tate.Index (fun _ => True),
        Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muEtale
    CMCoarseLevelFiniteOrder D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility
      h (𝟙 _) (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers htor hp.torsionUnits
      hp.pairAdditivity U

/-- The remaining finite-order target at the original sufficiently small levels. -/
def CMSmallLevelFiniteOrderStatement : Prop :=
  ∀ U : HarrisLevel D, D.rationalInvolution.LevelSufficientlySmall U →
    CMGeometricCoarseFiniteOrder D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U

/-- Actual finite order at the admitted small-level objects and injectivity
of the actual one-prime rational Tate action imply the exact rigidity target. -/
theorem cmSmallLevelRigidity_of_finiteOrder_and_primeFaithfulness
    (hfinite : CMSmallLevelFiniteOrderStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h htor)
    (hfaith : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
      (B : AbelianScheme (Spec (CommRingCat.of Ω))) (l : ℕ) [Fact l.Prime],
      Function.Injective (PrimeAdic.rationalHomMap (A := B) (B := B)
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) l)) :
    CMSmallLevelRigidityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor := by
  intro U hsmall Ω _ _ p hp
  let : ∀ k : Index (fun _ => True),
      IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muFinite
  let : ∀ k : Index (fun _ => True),
      Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muEtale
  let φ : F →+* Ω := ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop ≫
    (Scheme.ΓSpecIso (.of Ω)).hom).hom
  let : CharZero Ω := charZero_of_injective_ringHom φ.injective
  let := auxiliaryStarRing D C
  intro X hX hnX a q e he hfixed
  have hfin := hfinite U hsmall Ω p hp X hX hnX a q e he hfixed
  obtain ⟨v, hv⟩ := hsmall
  have hop := selfIsoPrimeTateOperator_eq_id_of_levelIso_fixed D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality compatibility h (𝟙 (Spec (CommRingCat.of Ω)))
    (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers htor hp.torsionUnits
    hp.pairAdditivity X U v hv a q e he hfixed hfin
  apply Iso.ext
  apply RationalAlgebraAction.hom_ext
  apply hfaith Ω X.actionObj.abelianScheme (Rat.HeightOneSpectrum.primesEquiv v).val
  change PrimeAdic.rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
      (Rat.HeightOneSpectrum.primesEquiv v).val (RationalAlgebraAction.hom0 e.hom) =
    PrimeAdic.rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
      (Rat.HeightOneSpectrum.primesEquiv v).val
      (Rationalization.identity X.actionObj.abelianScheme)
  rw [PrimeAdic.rationalHomMap_identity]
  exact hop

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
