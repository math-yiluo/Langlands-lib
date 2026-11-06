import Langlands.Shimura.PEL.HarrisIntegralLatticeOrder
import Langlands.Shimura.PEL.PolarizedWeilIntegralClasses
import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionProof

/-! # Recovering the actual Harris order action from normalized Tate images -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
    (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "Full" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation "toRat" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp
    (Over.mk s) (fun _ => True)
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality

omit [IsScalarTower ℚ F A] in
/-- An original normalized frame makes every original order element preserve
the full integral Tate image on the same actual abelian scheme. -/
theorem harrisIntegralFrame_order_full_image (X : PObj) (eta : Frame X)
    (hn : letI := auxiliaryStarRing D C
      HarrisIntegralFrameCondition D C P compatibility h s X eta) (a : O) :
    letI := auxiliaryStarRing D C
    ∀ b : Full X, ∃ c : Full X,
      Tate.rationalHomMap (Over.mk s) (fun _ => True) (X.actionObj.action a)
        ((toRat X) b) = (toRat X) c := by
  let := auxiliaryStarRing D C
  have hl := (harrisIntegralFrameCondition_iff_lattice
    D C P compatibility h s X eta).mp hn
  intro b
  have hb : (toRat X) b ∈ lattice X eta := by
    change (toRat X) b ∈ (lattice X eta : Set (Rat X))
    rw [hl]
    exact ⟨b, rfl⟩
  have hc := harrisIntegralFrameLattice_order_mem D C P compatibility h s X eta a hb
  change Tate.rationalHomMap (Over.mk s) (fun _ => True) (X.actionObj.action a)
    ((toRat X) b) ∈ (lattice X eta : Set (Rat X)) at hc
  rw [hl] at hc
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, hc.symm⟩

variable [IsLocallyNoetherian S] [ConnectedSpace S] [IsAlgClosed Ω]
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

/-- The original normalized frame recovers an actual integral action on the
same representative, with exactly its original rational action on the order. -/
def harrisIntegralFrameActionRestriction (X : PObj) (eta : Frame X)
    (hn : letI := auxiliaryStarRing D C
      HarrisIntegralFrameCondition D C P compatibility h s X eta) :
    letI := auxiliaryStarRing D C
    Restriction O X := by
  letI := auxiliaryStarRing D C
  let α : O →+* Rationalization.End X.actionObj.abelianScheme :=
    X.actionObj.action.toRingHom.comp (O).subtype
  have hex : ∀ a : O, ∃ g : CategoryTheory.End X.actionObj.abelianScheme,
      Rationalization.ofHom g = α a := by
    intro a
    exact Tate.exists_ofHom_eq_of_full_image htor hu s (α a)
      (harrisIntegralFrame_order_full_image D C P compatibility h s X eta hn a)
  let g : O → CategoryTheory.End X.actionObj.abelianScheme := fun a =>
    Classical.choose (hex a)
  have hg : ∀ a : O,
      Rationalization.ofEnd X.actionObj.abelianScheme (g a) = α a :=
    fun a => Classical.choose_spec (hex a)
  refine {
    action := {
      toFun := g
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
    agrees := hg }
  · apply Tate.ofHom_injective hu X.actionObj.abelianScheme X.actionObj.abelianScheme
    change Rationalization.ofEnd _ (g 1) = Rationalization.ofEnd _ 1
    rw [hg, map_one, map_one]
  · intro a b
    apply Tate.ofHom_injective hu X.actionObj.abelianScheme X.actionObj.abelianScheme
    change Rationalization.ofEnd _ (g (a * b)) = Rationalization.ofEnd _ (g a * g b)
    rw [hg, α.map_mul a b,
      (Rationalization.ofEnd X.actionObj.abelianScheme).map_mul (g a) (g b), hg, hg]
  · apply Tate.ofHom_injective hu X.actionObj.abelianScheme X.actionObj.abelianScheme
    change Rationalization.ofEnd _ (g 0) = Rationalization.ofEnd _ 0
    rw [hg, map_zero, map_zero]
  · intro a b
    apply Tate.ofHom_injective hu X.actionObj.abelianScheme X.actionObj.abelianScheme
    change Rationalization.ofEnd _ (g (a + b)) = Rationalization.ofEnd _ (g a + g b)
    rw [hg, α.map_add a b,
      (Rationalization.ofEnd X.actionObj.abelianScheme).map_add (g a) (g b), hg, hg]

omit [IsScalarTower ℚ F A] [QuasiSeparatedSpace S]
    [IsLocallyNoetherian S] [ConnectedSpace S] [IsAlgClosed Ω] in
include hu in
/-- Any two integral restrictions of the unchanged rational action have the
same actual endomorphism for every element of the original order. -/
theorem harrisIntegralActionRestriction_unique (X : PObj) :
    letI := auxiliaryStarRing D C
    ∀ a b : Restriction O X, a.action = b.action := by
  let := auxiliaryStarRing D C
  intro a b
  ext x
  apply Tate.ofHom_injective hu X.actionObj.abelianScheme X.actionObj.abelianScheme
  exact (a.agrees x).trans (b.agrees x).symm

variable
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X

/-- The original existential normalization of a fixed level orbit suffices
to recover the integral order action on that very representative. -/
def harrisIntegralLevelActionRestriction (X : PObj) (K : Level)
    (x : (tower X).obj K)
    (hn : letI := auxiliaryStarRing D C
      HarrisIntegralLevelCondition D C P compatibility h s hs htor hu X K x) :
    letI := auxiliaryStarRing D C
    Restriction O X := by
  letI := auxiliaryStarRing D C
  let eta := Classical.choose hn
  have hnorm := (Classical.choose_spec hn).1
  exact harrisIntegralFrameActionRestriction D C P compatibility h s htor hu X eta hnorm

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
