import Langlands.Shimura.PEL.HarrisTaylorCMDvrGoodModelReduction
import Langlands.Shimura.PEL.HarrisTaylorCMDivisionPremiseStatements
import Langlands.Shimura.PEL.HarrisTaylorCMStrictLocalMonodromy
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelMonodromy
import Langlands.Shimura.PEL.PolarizedWeilLevelPointTransport
import Langlands.AbelianScheme.NeronOggShafarevichStatement
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof

/-! # Division-case valuative existence from potential good reduction and the
Néron–Ogg–Shafarevich criterion -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

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

local notation "connTest" => connectedSpecTest D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality

omit [IsCMField F] [IsScalarTower ℚ F A] in
include C preservation composition unitCoherence associativity comparison symmetry stability
  square universality in
/-- On a connected admissible spectrum of a ring, every positive integer is a unit of
the ring. -/
private theorem isUnit_natCast_of_connTest (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (β : Spec (.of R) ⟶ Spec (.of F)) (k : ℕ) (hk : 0 < k) :
    IsUnit (k : R) := by
  simpa only [map_natCast] using
    ((connTest R β).property.torsionUnits ⟨k, hk, trivial⟩).map
      (Scheme.ΓSpecIso (.of R)).hom.hom

include dualityNaturality polarizationStability in
/-- In the division case, potential semistable reduction, the abelian reduction
criterion and the Néron–Ogg–Shafarevich criterion give good models of the level
representatives at every small level. -/
theorem cmLevelDvrGoodModel_of_division
    (hsemi : PotentialSemistableReductionStatement.{0})
    (habelian : AbelianReductionStatement.{0})
    (hnos : NeronOggShafarevichStatement.{0})
    (hD : D.IsDivision) (U : SmallCMLevel D) :
    CMLevelDvrGoodModelStatement D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h htor U := by
  let := auxiliaryStarRing D C
  intro V K _ _ _ _ _ _ β a x hx hnx
  obtain ⟨v, hv⟩ := U.property
  let j := Spec.algebraMap V K
  let TK := connTest K (j ≫ β)
  let B := x.1.actionObj.abelianScheme
  have hdim : B.HasRelativeDimension (Module.finrank ℚ E * n ^ 2) :=
    ((determinantDimensionCondition_iff D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (j ≫ β) x.1).mpr
      ⟨hx, hnx⟩).2
  let ℓ : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
  have hℓ : IsUnit ((ℓ.val : ℕ) : V) :=
    isUnit_natCast_of_connTest D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality V β ℓ.val ℓ.property.pos
  refine hnos V K B ℓ.val hℓ ?_
  intro W _ _ _ _ _ _ _ _ Lf _ _ _ _ _ Ω _ _ s hu g
  let bL : (connTest Lf (Spec.algebraMap K Lf ≫ j ≫ β)).obj.left ⟶ TK.obj.left :=
    Spec.algebraMap K Lf
  let TL := connTest Lf (Spec.algebraMap K Lf ≫ j ≫ β)
  let sL : Spec (.of Ω) ⟶ TL.obj.left := s
  let BL := (Langlands.AbelianScheme.baseChange bL).obj B
  let aL : A →ₐ[ℚ] End0 BL := (rationalBaseChangeEnd bL B).comp x.1.actionObj.action
  have hdimL : BL.HasRelativeDimension (Module.finrank ℚ E * n ^ 2) :=
    hasRelativeDimension_baseChange B _ hdim bL
  have hpot := Langlands.Shimura.HarrisTaylor.divisionPotentialGoodReduction D hsemi habelian
    hD (V := W) (K := Lf) BL aL hdimL
  have : CharZero (ResidueField W) := by
    refine charZero_of_inj_zero (fun k hk => ?_)
    by_contra hk0
    have hunit : IsUnit (k : W) := by
      simpa only [map_natCast] using
        (isUnit_natCast_of_connTest D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality V β k
          (Nat.pos_of_ne_zero hk0)).map (algebraMap V W)
    have hres := hunit.map (residue W)
    rw [map_natCast, hk] at hres
    exact not_isUnit_zero hres
  let huL := TL.property.torsionUnits
  let m := hpot.strictLocalMonodromyExponent s torsionFiniteEtale (fun _ => True) huL
  let hsL : ∀ Y : Cover TL.obj.left, Finite (Fiber sL Y) := geometricFiberFinite s
  let t : Spec (.of Ω) ⟶ TK.obj.left := sL ≫ bL
  let ht : ∀ Y : Cover TK.obj.left, Finite (Fiber t Y) := geometricFiberFinite t
  let path := Classical.choice (geometricPathExists a.hom t a.finiteFibers ht)
  let x' := PolarizedWeilLevel.pointMapData preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor TK.property.torsionUnits path
    ((hodgeLevelFunctor D C).obj U.obj) x
  let dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := TK.obj.left),
      PositivePullbackDualData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality bL X := fun X =>
    dualEvaluationDataOfGeometry preservation stability _
      (relativeDualSchemeExistence _ _) (relativeDualSchemeGeometry _ _ _)
  let y := levelDataBaseChange D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    bL compatibility h sL hsL ht htor TK.property.torsionUnits huL dualData U.obj x'
  have hfin : IsOfFinOrder (Tate.rationalMonodromyRepresentation sL hsL htor
      y.1.actionObj.abelianScheme (fun _ => True) huL g) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m.val, m.property.1, m.property.2 g⟩
  exact primeTateMonodromyAt_eq_one_of_smallLevel sL hsL htor huL D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h y.1 U.obj v hv y.2 g hfin

/-- Division-case valuative existence follows from potential semistable reduction, the
abelian reduction criterion and the Néron–Ogg–Shafarevich criterion, all in universe
zero. -/
def DivisionCMDiscreteValuativeReductionStatement : Prop :=
  PotentialSemistableReductionStatement.{0} → AbelianReductionStatement.{0} →
    NeronOggShafarevichStatement.{0} →
    DivisionCMDiscreteValuativeExistenceStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor

/-- The reduction holds: good models at small levels give valuative existence. -/
theorem divisionCMDiscreteValuativeReduction :
    DivisionCMDiscreteValuativeReductionStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := by
  intro hsemi habelian hnos hD U
  exact cmLevelDiscreteValuativeExistence_of_goodModels D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor U
    (cmLevelDvrGoodModel_of_division D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor hsemi habelian hnos hD U)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
