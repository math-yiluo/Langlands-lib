import Langlands.Shimura.PEL.HarrisTaylorCMPowerLattice
import Langlands.AbelianScheme.Tate.RealizedLatticeStabilizer
import Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationFibreAffine
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenProof
import Langlands.AlgebraicGeometry.FiniteEtale.IdentityPoint

/-! # An integral isogenous model for an even power of a CM self-isogeny -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)

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
  (P : Prerequisites.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

variable
  (hs : ∀ Y : Cover (Spec (CommRingCat.of Ω)), Finite (Fiber (𝟙 (Spec (CommRingCat.of Ω))) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ((Spec (CommRingCat.of Ω)), ⊤)))
  (X : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := (Spec (CommRingCat.of Ω))))

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Frame" => WeilAdelicFrame P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability X.hasDual X.geometry X.inversePoincare
  X.evaluation compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) (𝟙 (Spec (CommRingCat.of Ω)))
local notation "Rat" => Rational X.actionObj.abelianScheme (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True)
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h (𝟙 (Spec (CommRingCat.of Ω))) X

omit [IsScalarTower ℚ F A] in
include hs htor hu in
/-- The literal lattice of every compatible Harris frame at the identity field
point is the full integral Tate image of an actual isogenous abelian scheme. -/
theorem harrisCMFrameLattice_realized :
    letI := auxiliaryStarRing D C
    ∀ eta : Frame,
      ∃ (B : AbelianScheme (Spec (CommRingCat.of Ω))) (r : Rationalization.of B ≅
          Rationalization.of X.actionObj.abelianScheme),
        ∀ w : Rat, w ∈ lattice eta ↔
          ∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))),
            rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) r.hom
              (GroupScheme.Tate.toRational B.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) x) = w := by
  let := auxiliaryStarRing D C
  intro eta
  let W : DualWitness X.actionObj.abelianScheme :=
    ⟨X.hasDual, X.geometry, X.inversePoincare, X.evaluation⟩
  have hfib := W.forall_finset_fibre_affine P properFibreAmpleAffineOpen
    X.polarization X.isPolarization
  let := finiteAdeleModule X.actionObj.abelianScheme (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) h
  let : Module Rf Rat := Module.compHom _ (Rf).subtype
  apply commensurableInvariantLatticeRealization htor h (Spec (CommRingCat.of Ω)) hu Ω (𝟙 (Spec (CommRingCat.of Ω))) hs
    X.actionObj.abelianScheme hfib (lattice eta)
  · intro gamma w
    rw [fundamentalGroup_identity_eq_one hs gamma]
    simp only [rationalMonodromy_apply, rationalMonodromyMap_one]
  · exact harrisIntegralFrameLattice_integerBounds D C P compatibility h (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu X eta

/-- An actual compatible frame is exactly realized by a rational model, on
which a positive even power is an actual integral automorphism. -/
def IntegralPowerModelWitness :
    letI := auxiliaryStarRing D C
    ∀ (_q : ℚˣ) (_e : X.actionObj ≅ X.actionObj), Prop := by
  let := auxiliaryStarRing D C
  intro q e
  let u : Aut (Rationalization.of X.actionObj.abelianScheme) :=
    RationalAlgebraAction.underlyingIso e
  exact ∃ (eta : Frame) (m : ℕ), 0 < m ∧ q ^ (2 * m) = 1 ∧
    ∃ (B : AbelianScheme (Spec (CommRingCat.of Ω)))
      (r : Rationalization.of B ≅ Rationalization.of X.actionObj.abelianScheme)
      (g : B ≅ B),
      (∀ w : Rat, w ∈ lattice eta ↔
        ∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))),
          rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) r.hom
            (GroupScheme.Tate.toRational B.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) x) = w) ∧
      Rationalization.ofHom g.hom = r.hom ≫
        (u ^ (2 * m)).hom ≫ r.inv ∧
      Rationalization.ofHom g.inv = r.hom ≫
        (u ^ (2 * m)).inv ≫ r.inv

variable
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom]
  (additivity : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := (Spec (CommRingCat.of Ω))))

local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "orbitTower" => PolarizedWeilLevel.levelTower P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu additivity
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  additivity

omit [IsScalarTower ℚ F A] in
/-- Every fixed orbit at an original compact Harris level has an integral
isogenous model for a positive even power of its actual self-isogeny. -/
theorem integralPowerModelWitness_of_levelIso_fixed (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      IntegralPowerModelWitness D C P compatibility h Ω X q e := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed
  obtain ⟨eta, m, hm, hq, hstable⟩ := evenIntegralPowerWitness_of_levelIso_fixed
    D C P compatibility h (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu additivity X U a q e he hfixed
  obtain ⟨B, r, hr⟩ := harrisCMFrameLattice_realized
    D C P compatibility h Ω hs htor hu X eta
  let u : Aut (Rationalization.of X.actionObj.abelianScheme) :=
    RationalAlgebraAction.underlyingIso e
  let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
  have hpow : (u ^ (2 * m)).hom = f ^ (2 * m) :=
    map_pow (Aut.toEnd _) _ _
  let := finiteAdeleModule X.actionObj.abelianScheme (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) h
  let : Module Rf Rat := Module.compHom _ (Rf).subtype
  have hstable' : ∀ w : Rat, rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True)
      (u ^ (2 * m)).hom w ∈ lattice eta ↔
      w ∈ lattice eta := by
    intro w
    rw [hpow]
    exact hstable w
  obtain ⟨g, hg, hgi⟩ := realizedLatticeStabilizer htor (Spec (CommRingCat.of Ω)) hu Ω (𝟙 (Spec (CommRingCat.of Ω)))
    X.actionObj.abelianScheme B r (lattice eta).toAddSubgroup hr
    (u ^ (2 * m)) hstable'
  exact ⟨eta, m, hm, hq, B, r, g, hr, hg, hgi⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
