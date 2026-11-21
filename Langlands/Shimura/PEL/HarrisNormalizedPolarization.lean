import Langlands.Shimura.PEL.HarrisIntegralFrameReduction
import Langlands.Shimura.PEL.HarrisIntegralSourceResidues
import Langlands.Shimura.PEL.HarrisIntegralOrderedFullLevel
import Langlands.AbelianScheme.Tate.PrimitiveHom

/-! # Primitive normalized polarizations of Harris data -/

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
open Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)
local notation "Stab" => (harrisIntegralAdeleStabilizer D C : Subgroup G)
local notation "op" => ScalarExtensionSimilitudePoints.operator
local notation "K" => harrisIntegralAdeleCongruence D C
local notation "multiples" => harrisIntegralSourceMultiples D C
local notation "integralOp" => harrisIntegralSourceOperator D C
local notation "reduceOp" => harrisIntegralSourceReduction D C

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
  h (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation:max "Full" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation:max "toRat" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True)
local notation:max "rat_injective" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.full_toRational_injective (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation:max "Level" X:max m:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Level (X).actionObj.abelianScheme.toGrp (Over.mk s) (m : ℕ)
local notation:max "eval" X:max m:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.evaluation (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True) m

local notation "L" => D.harrisHodgePELIntegralLattice C
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "polOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).polarization
local notation:max "DOf" X:max =>
  letI := auxiliaryStarRing D C
  dualAbelianSchemeFromEvaluation (X).actionObj.abelianScheme (X).hasDual (X).geometry
    P.preservation (X).inversePoincare (X).evaluation P.stability P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry

/-- The actual integral source lattice has positive rank. -/
theorem harrisIntegralLattice_finrank_pos : 0 < Module.finrank ℤ L := by
  rw [harrisIntegralSource_rank D C]
  have hE : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hn : 0 < n := lt_trans Nat.zero_lt_one D.rank_gt_one
  positivity

/-- A primitive actual homomorphism of which the polarization of `X` is a positive
multiple. -/
def HarrisPrimitivePolarization (X : PObj) (lam0 : BOf X ⟶ DOf X) : Prop :=
  letI := auxiliaryStarRing D C
  Tate.IsPrimitiveHom lam0 ∧ ∃ k : ℕ, 0 < k ∧ k • lam0 = X.polarization

section Geometric

variable [IsLocallyNoetherian S] [ConnectedSpace S] [IsAlgClosed Ω]
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

omit [IsLocallyNoetherian S] [ConnectedSpace S] in
include hu in
/-- For a polarized Harris action with a normalized frame at an algebraically closed
point, every positive integer dividing the polarization is bounded by the number of
geometric kernel points of the polarization. -/
theorem harrisPolarization_divisor_le (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (k : ℕ) (lam0 : BOf X ⟶ DOf X) (hk : 0 < k) (hklam0 : k • lam0 = polOf X) :
    k ≤ Nat.card (GroupScheme.pointsHom (groupHom (polOf X)) (Over.mk s)).ker := by
  let := auxiliaryStarRing D C
  let m : Index (fun _ => True) := ⟨k, hk, trivial⟩
  let m' : ℕ+ := ⟨k, hk⟩
  have hfin : Finite (GroupScheme.pointsHom (groupHom X.polarization) (Over.mk s)).ker :=
    GroupScheme.IsIsogeny.finite_ker_pointsHom s X.isPolarization.1
  let f : Level X m.val →
      (GroupScheme.pointsHom (groupHom X.polarization) (Over.mk s)).ker := fun x =>
    ⟨(Additive.toMul x).val, by
      have hz := Tate.levelMap_nsmul_self (Over.mk s) lam0 k x
      rw [hklam0] at hz
      have hz' := congrArg (fun z => (Additive.toMul (GroupScheme.Tate.toSection _ _ _ z)))
        hz
      exact hz'⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply GroupScheme.Tate.toSection_injective (BOf X).toGrp (Over.mk s) k
    exact congrArg (fun z => Additive.ofMul z.val) hxy
  have hcard := Nat.card_le_card_of_injective f hf
  have hlev : Nat.card (Level X m.val) = k ^ Module.finrank ℤ L := by
    let e : Level X m.val ≃ (Fin (Module.finrank ℤ L) → ZMod k) :=
      (harrisIntegralFrameTorsionEquiv D C P compatibility h s hu X m eta hn).toEquiv.symm.trans
        (harrisIntegralReducedSourceCoordinates D C h m').toEquiv
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [hlev] at hcard
  exact le_trans (Nat.le_self_pow (harrisIntegralLattice_finrank_pos D C).ne' k) hcard

variable (htor : TorsionFiniteEtaleStatement.{0})

omit [IsLocallyNoetherian S] [ConnectedSpace S] in
include hu in
/-- A polarized Harris action with a normalized frame at an algebraically closed point
has a primitive polarization. -/
theorem exists_harrisPrimitivePolarization (X : PObj) (eta : Frame X)
    (hn : Normalized X eta) : ∃ lam0 : BOf X ⟶ DOf X, HarrisPrimitivePolarization D C P X lam0 := by
  let := auxiliaryStarRing D C
  obtain ⟨k, lam0, hk, hklam0, hprim⟩ := Tate.exists_isPrimitiveHom_nsmul_eq X.polarization
    (Nat.card (GroupScheme.pointsHom (groupHom X.polarization) (Over.mk s)).ker)
    (fun k g hk hkg => harrisPolarization_divisor_le D C P compatibility h s hu X eta hn k g hk
      hkg)
  exact ⟨lam0, hprim, k, hk, hklam0⟩

omit [QuasiSeparatedSpace S] in
include htor hu s in
/-- The primitive polarization of a polarized Harris action on a connected base is
unique. -/
theorem harrisPrimitivePolarization_unique (X : PObj) {lam0 lam1 : BOf X ⟶ DOf X}
    (hlam0 : HarrisPrimitivePolarization D C P X lam0)
    (hlam1 : HarrisPrimitivePolarization D C P X lam1) : lam0 = lam1 := by
  obtain ⟨hp, k, hk, hklam0⟩ := hlam0
  obtain ⟨hp', k', hk', hklam1⟩ := hlam1
  exact (Tate.eq_of_nsmul_eq_nsmul_of_isPrimitiveHom htor hu s hk hk' hp hp'
    (hklam0.trans hklam1.symm)).2

end Geometric

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
