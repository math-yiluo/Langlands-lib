import Langlands.Shimura.PEL.HarrisIntegralFrameReduction
import Langlands.AbelianScheme.Tate.WeilFrameMonodromy
import Langlands.AbelianScheme.Tate.WeilGeometricTransportProof

/-! # Geometric monodromy on the finite reduction of Harris frames -/

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
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
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

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation "Π" => FundamentalGroup s hs
local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation compatibility (X).polarization h (X).actionObj.action A
    (D.harrisHodgePELForm C) s
local notation "RAct" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
    (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
    h (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "LAct" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation (X).polarization h (X).actionObj.action A (D.harrisHodgePELForm C)
    s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "CommAct" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation (X).polarization h (X).actionObj.action A (D.harrisHodgePELForm C)
    s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "full" X:max => harrisIntegralFrameFull D C P compatibility h s X
local notation:max "red" X:max => harrisIntegralFrameReduction D C P compatibility h s X
local notation:max "intMon" X:max => Tate.integralMonodromy s hs htor (BOf X) (fun _ => True) hu
local notation:max "ratMon" X:max => Tate.rationalMonodromy s hs htor (BOf X) (fun _ => True) hu
local notation:max "finMon" X:max m:max =>
  Tate.levelMonodromy s hs htor (BOf X) (m : Index (fun _ => True)).val (m).property.1 (hu m)

/-- The original monodromy action preserves the actual normalized frame condition. -/
theorem harrisIntegralFrameCondition_monodromy (X : PObj) (eta : Frame X)
    (hn : Normalized X eta) (gamma : Π) :
    letI : MulAction Π (Frame X) := LAct X
    Normalized X (gamma • eta) := by
  let := auxiliaryStarRing D C
  let _ : MulAction Π (Frame X) := LAct X
  intro v
  refine (hn v).trans ?_
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨intMon X gamma x, (Tate.toRational_monodromy s hs htor (BOf X) _ hu gamma x).trans
      (congrArg (ratMon X gamma) hx)⟩
  · rintro ⟨x, hx⟩
    refine ⟨(intMon X gamma).symm x, (ratMon X gamma).injective ?_⟩
    rw [← Tate.toRational_monodromy, AddEquiv.apply_symm_apply]
    exact hx

/-- The finite reduction of the original geometric translate is the finite
level monodromy of the original reduction, on each source residue. -/
theorem harrisIntegralFrameReduction_monodromy (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) (gamma : Π) :
    letI : MulAction Π (Frame X) := LAct X
    ∀ (hn' : Normalized X (gamma • eta)) (q : HarrisIntegralSourceMod D C m.val),
      red X m (gamma • eta) hn' q = finMon X m gamma (red X m eta hn q) := by
  let := auxiliaryStarRing D C
  let _ : MulAction Π (Frame X) := LAct X
  intro hn' q
  obtain ⟨v, rfl⟩ := (harrisIntegralSourceMultiples D C m.val).mkQ_surjective q
  rw [harrisIntegralFrameReduction_mkQ, harrisIntegralFrameReduction_mkQ]
  have hf : full X (gamma • eta) hn' v = intMon X gamma (full X eta hn v) := by
    apply GroupScheme.Tate.full_toRational_injective (BOf X).toGrp (Over.mk s)
    rw [Tate.toRational_monodromy, harrisIntegralFrameFull_toRational,
      harrisIntegralFrameFull_toRational]
    rfl
  rw [hf]
  exact Tate.evaluation_integralMonodromyHom s hs htor (BOf X) _ hu gamma m _

variable [IsAlgClosed Ω]

/-- An invariant normalized right orbit at a subgroup contained in the principal
congruence subgroup reduces to pointwise monodromy-fixed finite torsion. -/
theorem harrisIntegralFrameReduction_fixed_of_le (X : PObj) (m : Index (fun _ => True))
    (U : Subgroup G) (hU : U ≤ Cong m.val) (eta : Frame X) (hn : Normalized X eta) :
    letI : MulAction Gᵐᵒᵖ (Frame X) := RAct X
    letI : MulAction Π (Frame X) := LAct X
    letI : SMulCommClass Π Gᵐᵒᵖ (Frame X) := CommAct X
    RightOrbit.mk U eta ∈ MulAction.fixedPoints Π (RightOrbit (Frame X) U) →
      ∀ (gamma : Π) (q : HarrisIntegralSourceMod D C m.val),
        finMon X m gamma (red X m eta hn q) = red X m eta hn q := by
  let _ : MulAction Gᵐᵒᵖ (Frame X) := RAct X
  let _ : MulAction Π (Frame X) := LAct X
  let _ : SMulCommClass Π Gᵐᵒᵖ (Frame X) := CommAct X
  intro hfix gamma q
  obtain ⟨g, hg, hgamma⟩ := (RightOrbit.mk_mem_fixedPoints (Γ := Π) U eta).mp hfix gamma
  have heq := (RightOrbit.mk_eq_mk (Cong m.val) eta (gamma • eta)).mpr ⟨g, hU hg, hgamma⟩
  have hn' := harrisIntegralFrameCondition_monodromy D C P compatibility h s hs htor hu X eta hn gamma
  have hr := (harrisIntegralFrameReduction_eq_iff_rightOrbit D C P compatibility h s hu X m
    eta (gamma • eta) hn hn').mpr heq
  exact (harrisIntegralFrameReduction_monodromy D C P compatibility h s hs htor hu X m
    eta hn gamma hn' q).symm.trans (DFunLike.congr_fun hr q).symm

/-- At exactly the principal congruence subgroup, pointwise fixed finite torsion
values are also sufficient for invariance of the original right orbit. -/
theorem harrisIntegralFrameReduction_fixed_iff (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) :
    letI : MulAction Gᵐᵒᵖ (Frame X) := RAct X
    letI : MulAction Π (Frame X) := LAct X
    letI : SMulCommClass Π Gᵐᵒᵖ (Frame X) := CommAct X
    RightOrbit.mk (Cong m.val) eta ∈ MulAction.fixedPoints Π (RightOrbit (Frame X) (Cong m.val)) ↔
      ∀ (gamma : Π) (q : HarrisIntegralSourceMod D C m.val),
        finMon X m gamma (red X m eta hn q) = red X m eta hn q := by
  let _ : MulAction Gᵐᵒᵖ (Frame X) := RAct X
  let _ : MulAction Π (Frame X) := LAct X
  let _ : SMulCommClass Π Gᵐᵒᵖ (Frame X) := CommAct X
  refine ⟨harrisIntegralFrameReduction_fixed_of_le D C P compatibility h s hs htor hu X m
    (Cong m.val) le_rfl eta hn, ?_⟩
  intro hf
  apply (RightOrbit.mk_mem_fixedPoints (Γ := Π) (Cong m.val) eta).mpr
  intro gamma
  have hn' := harrisIntegralFrameCondition_monodromy D C P compatibility h s hs htor hu X eta hn gamma
  apply (RightOrbit.mk_eq_mk (Cong m.val) eta (gamma • eta)).mp
  apply (harrisIntegralFrameReduction_eq_iff_rightOrbit D C P compatibility h s hu X m
    eta (gamma • eta) hn hn').mp
  apply AddMonoidHom.ext
  intro q
  exact ((harrisIntegralFrameReduction_monodromy D C P compatibility h s hs htor hu X m
    eta hn gamma hn' q).trans (hf gamma q)).symm

local notation:max "FiniteTorsion" X:max m:max =>
  GroupScheme.Tate.Level (BOf X).toGrp (Over.mk s) (m : Index (fun _ => True)).val

/-- The additive subgroup of the actual finite torsion fixed by geometric monodromy. -/
def harrisIntegralFixedTorsion (X : PObj) (m : Index (fun _ => True)) :
    AddSubgroup (FiniteTorsion X m) where
  carrier := {t | ∀ gamma : Π, finMon X m gamma t = t}
  zero_mem' gamma := map_zero (finMon X m gamma)
  add_mem' {a b} ha hb gamma := (map_add (finMon X m gamma) a b).trans
    (congrArg₂ (· + ·) (ha gamma) (hb gamma))
  neg_mem' {a} ha gamma := (map_neg (finMon X m gamma) a).trans
    (congrArg Neg.neg (ha gamma))

local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation:max "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "LevelNormalized" => HarrisIntegralLevelCondition D C P compatibility h s hs htor hu
local notation "FT" => harrisIntegralFixedTorsion D C P s hs htor hu

/-- Reduce an actual invariant, normalized level orbit to the fixed subgroup of
finite torsion whenever its level subgroup is contained in the congruence kernel. -/
def harrisIntegralLevelReduction (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (tower X).obj U)
    (hx : LevelNormalized X U x) : HarrisIntegralSourceMod D C m.val →+ FT X m := by
  let _ : MulAction Gᵐᵒᵖ (Frame X) := RAct X
  let eta : Frame X := Classical.choose hx
  have hn : Normalized X eta := (Classical.choose_spec hx).1
  have he : RightOrbit.mk (U.toSubgroup : Subgroup G) eta = x.1 := (Classical.choose_spec hx).2
  exact (red X m eta hn).codRestrict (FT X m) (fun q gamma =>
    harrisIntegralFrameReduction_fixed_of_le D C P compatibility h s hs htor hu X m
      U.toSubgroup hU eta hn (he.symm ▸ x.2) gamma q)

/-- Evaluation of the orbit reduction uses any normalized representative of the
same original invariant orbit, not a particular frame choice. -/
theorem harrisIntegralLevelReduction_apply (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (tower X).obj U)
    (hx : LevelNormalized X U x) (eta : Frame X) (hn : Normalized X eta) :
    letI : MulAction Gᵐᵒᵖ (Frame X) := RAct X
    RightOrbit.mk (U.toSubgroup : Subgroup G) eta = x.1 →
      ∀ q : HarrisIntegralSourceMod D C m.val,
        (harrisIntegralLevelReduction D C P compatibility h s hs htor hu X m U hU x hx q).val =
          red X m eta hn q := by
  let _ : MulAction Gᵐᵒᵖ (Frame X) := RAct X
  intro heta q
  let xi : Frame X := Classical.choose hx
  have hnxi : Normalized X xi := (Classical.choose_spec hx).1
  have hxi : RightOrbit.mk (U.toSubgroup : Subgroup G) xi = x.1 := (Classical.choose_spec hx).2
  obtain ⟨g, hg, he⟩ := (RightOrbit.mk_eq_mk (U.toSubgroup : Subgroup G) xi eta).mp
    (hxi.trans heta.symm)
  have heq := (RightOrbit.mk_eq_mk (Cong m.val) xi eta).mpr ⟨g, hU hg, he⟩
  exact DFunLike.congr_fun ((harrisIntegralFrameReduction_eq_iff_rightOrbit
    D C P compatibility h s hu X m xi eta hnxi hn).mpr heq) q

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
