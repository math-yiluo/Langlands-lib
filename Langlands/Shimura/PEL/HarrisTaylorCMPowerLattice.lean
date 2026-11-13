import Langlands.Shimura.PEL.HarrisTaylorCMCompactMultiplier
import Langlands.Shimura.PEL.HarrisIntegralLatticeBounds

/-! # An even power preserving the actual carried Harris lattice -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)

private theorem exists_pos_pow_mem_open_of_compact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (H : OpenSubgroup G) (g : G) (hg : g ∈ K) :
    ∃ m : ℕ, 0 < m ∧ g ^ m ∈ H := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let J : OpenSubgroup K := H.comap K.subtype continuous_subtype_val
  have : Finite (K ⧸ J.toSubgroup) := inferInstance
  obtain ⟨m, hm, _, hmem⟩ := J.toSubgroup.exists_pow_mem_of_index_ne_zero
    J.toSubgroup.index_ne_zero_of_finite (⟨g, hg⟩ : K)
  exact ⟨m, hm, hmem⟩

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
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (additivity : PositivePairAdditivity D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality (S := S))
  (X : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := S))

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
local notation "orbitTower" => PolarizedWeilLevel.levelTower P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  additivity
local notation "Frame" => WeilAdelicFrame P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability X.hasDual X.geometry X.inversePoincare
  X.evaluation compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" => weilAdelicFrameRightAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability X.hasDual X.geometry
  X.inversePoincare X.evaluation compatibility X.polarization h X.actionObj.action
  A (D.harrisHodgePELForm C) s
local notation "frameIsogeny" => weilAdelicFrameIsogeny P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability X.hasDual X.hasDual
  X.geometry X.geometry X.inversePoincare X.evaluation X.inversePoincare X.evaluation
  (additivity X X) X.polarization X.polarization compatibility rationalWeilFunctoriality
  h X.actionObj.action X.actionObj.action A (D.harrisHodgePELForm C) s
local notation "Rat" => Rational X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s X

/-- A positive even power has multiplier one and preserves, in both directions,
the actual integral finite-adele lattice of one compatible Harris frame. -/
def EvenIntegralPowerWitness :
    letI := auxiliaryStarRing D C
    ∀ (_q : ℚˣ) (_e : X.actionObj ≅ X.actionObj), Prop := by
  let := auxiliaryStarRing D C
  intro q e
  let := finiteAdeleModule X.actionObj.abelianScheme (Over.mk s) (fun _ => True) h
  let : Module Rf Rat := Module.compHom _ (Rf).subtype
  let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
  exact ∃ (eta : Frame) (m : ℕ), 0 < m ∧ q ^ (2 * m) = 1 ∧
    ∀ w : Rat,
      rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
          (f ^ (2 * m)) w
        ∈ lattice eta ↔ w ∈ lattice eta

omit [IsScalarTower ℚ F A] in
/-- Any fixed orbit at an original compact Harris level supplies an actual
even-power lattice witness, without a finite-order premise. -/
theorem evenIntegralPowerWitness_of_levelIso_fixed (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      EvenIntegralPowerWitness D C P compatibility h s X q e := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed
  obtain ⟨eta, u, huU, hframe⟩ := exists_frame_original_element_of_levelIso_fixed
    D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability P.square P.universality compatibility h s hs htor hu
    additivity X U a q e he hfixed
  let : Module.Finite ℚ A := (hodgeRationalPELConditions D C).finite_module
  let g := scalarEquiv u
  let K := (indexFunctor).obj U
  have hg : g ∈ K.subgroup := (hodgeLevelFunctor_obj_mem D C U u).mpr huU
  obtain ⟨m, hm, hgm⟩ := exists_pos_pow_mem_open_of_compact K.subgroup K.isCompact
    (harrisIntegralAdeleOpenStabilizer D C) (g ^ 2) (K.subgroup.pow_mem hg 2)
  have hstab : g ^ (2 * m) ∈ harrisIntegralAdeleStabilizer D C := by
    change (g ^ 2) ^ m ∈ harrisIntegralAdeleStabilizer D C at hgm
    simpa only [pow_mul] using hgm
  have habs := abs_multiplier_eq_one_of_original_level_frame D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    P.square P.universality compatibility h s additivity X U q e he eta u huU hframe
  have hq2 : q ^ 2 = 1 := by
    apply Units.ext
    change (q : ℚ) ^ 2 = 1
    nlinarith [sq_abs (q : ℚ)]
  let := finiteAdeleModule X.actionObj.abelianScheme (Over.mk s) (fun _ => True) h
  let : Module Rf Rat := Module.compHom _ (Rf).subtype
  refine ⟨eta, m, hm, by rw [pow_mul, hq2, one_pow], ?_⟩
  let := scalarExtensionAlgebraModule A A Af
  let f := rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.hom0 e.hom)
  have hconj (x : Vf) : f (eta.1 x) = eta.1 (g.val.1 x) :=
    congrArg (fun xi : Frame => xi.1 x) hframe
  have hpow (k : ℕ) (x : Vf) :
      (f ^ k) (eta.1 x) = eta.1 ((g ^ k).val.1 x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ']
      change f ((f ^ k) (eta.1 x)) = eta.1 (g.val.1 ((g ^ k).val.1 x))
      rw [ih, hconj]
  intro w
  obtain ⟨x, rfl⟩ := eta.1.surjective w
  rw [map_pow, hpow]
  rw [harrisIntegralFrameLattice_apply_mem, harrisIntegralFrameLattice_apply_mem]
  exact hstab x

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
