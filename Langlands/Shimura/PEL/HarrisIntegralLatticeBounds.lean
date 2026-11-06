import Langlands.Shimura.PEL.HarrisIntegralLevelLattice
import Langlands.Shimura.PEL.HarrisIntegralSourceLevels
import Langlands.AbelianScheme.Tate.AdelicScalarTopology
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.OrderOfElement

/-! # Integer bounds for carried Harris Tate submodules -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Topology

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

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "L" => D.harrisHodgePELIntegralLattice C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C

private theorem adele_sigmaCompact
    (h : Global.RationalProfiniteIntegerAdeleComparison) : SigmaCompactSpace Af := by
  let K : ℚ → Set Af := fun q =>
    (fun a : Af => algebraMap ℚ Af q * a) '' (Rf : Set Af)
  refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact (Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id)
  · apply Set.eq_univ_of_forall
    intro z
    obtain ⟨q, hq, a, ha⟩ := Langlands.Topology.Rationalization.exists_chart
      ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm z)
    refine Set.mem_sUnion.mpr ⟨K q, ⟨q, rfl⟩, ?_⟩
    refine ⟨(Global.RationalProfiniteIntegerAdeleComparison.integralEquiv h a : Af),
      (Global.RationalProfiniteIntegerAdeleComparison.integralEquiv h a).property, ?_⟩
    change algebraMap ℚ Af q * (Global.RationalProfiniteIntegerAdeleComparison.integralEquiv h a : Af) = z
    rw [← Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv_tmul, ha,
      AlgEquiv.apply_symm_apply]

omit [IsScalarTower ℚ F A] in
include D C in
private theorem source_sigmaCompact
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    letI : TopologicalSpace Vf := moduleTopology Af Vf
    SigmaCompactSpace Vf := by
  let : TopologicalSpace Vf := moduleTopology Af Vf
  let : SigmaCompactSpace Af := adele_sigmaCompact h
  let : ContinuousAdd Vf := IsModuleTopology.toContinuousAdd Af Vf
  let b := (Module.finBasis ℤ L).extendOfIsLattice ℚ
  let : Module.Finite ℚ A := Module.Finite.of_basis b
  let e := (b.baseChange Af).equivFun
  have hc : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hs := isSigmaCompact_univ.image hc
  rw [Set.image_univ, Set.range_eq_univ.mpr e.symm.surjective] at hs
  exact isSigmaCompact_univ_iff.mp hs

omit [IsScalarTower ℚ F A] in
private theorem sourceSpan_fg :
    letI : Module Rf Vf := Module.compHom _ (Rf).subtype
    (Λf).FG := by
  let : Module Rf Vf := Module.compHom _ (Rf).subtype
  let b := Module.finBasis ℤ L
  let v : Fin (Module.finrank ℤ L) → Vf := fun i => (1 : Af) ⊗ₜ[ℚ] (b i : A)
  have he : Λf = Submodule.span Rf (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x]
      simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum,
        TensorProduct.tmul_smul]
      apply Submodule.sum_mem
      intro i _
      apply (Submodule.span Rf (Set.range v)).toAddSubgroup.zsmul_mem
      exact Submodule.subset_span ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact D.harrisHodgePELIntegralAdeleSpan_tmul C (b i)
  rw [he]
  exact Submodule.fg_span (Set.finite_range v)

omit [IsScalarTower ℚ F A] in
private theorem sourceSpan_compact :
    letI : TopologicalSpace Vf := moduleTopology Af Vf
    IsCompact (Λf : Set Vf) := by
  let : TopologicalSpace Vf := moduleTopology Af Vf
  let : Module Rf Vf := Module.compHom _ (Rf).subtype
  let : ContinuousAdd Vf := IsModuleTopology.toContinuousAdd Af Vf
  let : CompactSpace Rf := isCompact_iff_compactSpace.mp (Global.isCompact_integralFiniteAdeles ℚ)
  let : ContinuousSMul Rf Vf := MulAction.continuousSMul_compHom
    (f := (Rf).subtype.toMonoidHom) continuous_subtype_val
  exact Submodule.isCompact_of_fg (sourceSpan_fg D C)

variable (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

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
local notation "adelicModule" X:max =>
  letI := auxiliaryStarRing D C
  Tate.finiteAdeleModule (X).actionObj.abelianScheme (Over.mk s) (fun _ => True) h
local notation "tateTopology" X:max =>
  letI := auxiliaryStarRing D C
  Tate.rationalTopology (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s

private def frameFiniteAdeleMap (X : PObj) (eta : Frame X) :
    let := adelicModule X
    Vf →ₗ[Af] Rat X := by
  let := auxiliaryStarRing D C
  let := adelicModule X
  refine { eta.1.toAddMonoidHom with map_smul' := ?_ }
  intro r v
  have he := eta.1.map_smul (((1 : A) ⊗ₜ[ℚ] r)) v
  rw [scalarExtensionAlgebraModule_one_tmul_smul] at he
  change eta.1 (r • v) = Tate.rationalEndAction X.actionObj.abelianScheme
    (Over.mk s) (fun _ => True) (X.actionObj.action 1)
    (Tate.finiteAdeleAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True) h r
      (eta.1 v)) at he
  rw [map_one, map_one] at he
  exact he

omit [IsScalarTower ℚ F A] in
private theorem frame_continuous (X : PObj) (eta : Frame X) :
    letI : TopologicalSpace Vf := moduleTopology Af Vf
    letI := tateTopology X
    Continuous (fun v : Vf => eta.1 v) := by
  let := auxiliaryStarRing D C
  let : TopologicalSpace Vf := moduleTopology Af Vf
  let : TopologicalSpace (Rat X) := tateTopology X
  let := adelicModule X
  let : IsTopologicalAddGroup (Rat X) :=
    Tate.rationalFull_topologicalAddGroup X.actionObj.abelianScheme (Over.mk s)
  let : ContinuousSMul Af (Rat X) :=
    Tate.finiteAdeleModule_continuousSMul X.actionObj.abelianScheme (Over.mk s) h
  exact IsModuleTopology.continuous_of_linearMap
    (frameFiniteAdeleMap D C P compatibility h s X eta)

omit [IsScalarTower ℚ F A] in
/-- The actual carried frame submodule is compact in the existing rational Tate topology. -/
theorem harrisIntegralFrameLattice_isCompact (X : PObj) (eta : Frame X) :
    letI := tateTopology X
    IsCompact (lattice X eta : Set (Rat X)) := by
  let : TopologicalSpace Vf := moduleTopology Af Vf
  let : TopologicalSpace (Rat X) := tateTopology X
  change IsCompact ((fun v : Vf => eta.1 v) '' (Λf : Set Vf))
  exact (sourceSpan_compact D C).image (frame_continuous D C P compatibility h s X eta)

variable
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

omit [IsScalarTower ℚ F A] in
include hs htor hu in
/-- The actual carried frame submodule is open in the existing rational Tate topology. -/
theorem harrisIntegralFrameLattice_isOpen (X : PObj) (eta : Frame X) :
    letI := tateTopology X
    IsOpen (lattice X eta : Set (Rat X)) := by
  let := auxiliaryStarRing D C
  let : TopologicalSpace Vf := moduleTopology Af Vf
  let : TopologicalSpace (Rat X) := tateTopology X
  let : IsTopologicalAddGroup Vf := IsModuleTopology.isTopologicalAddGroup Af Vf
  let : SigmaCompactSpace Vf := source_sigmaCompact D C h
  let : IsTopologicalAddGroup (Rat X) :=
    Tate.rationalFull_topologicalAddGroup X.actionObj.abelianScheme (Over.mk s)
  let : T2Space (Rat X) := Tate.rationalFull_t2Space X.actionObj.abelianScheme (Over.mk s)
  let : LocallyCompactSpace (Rat X) :=
    Tate.rationalFull_locallyCompactSpace X.actionObj.abelianScheme s hs htor hu
  have he : IsOpenMap eta.1.toAddMonoidHom :=
    AddMonoidHom.isOpenMap_of_sigmaCompact eta.1.toAddMonoidHom eta.1.surjective
      (frame_continuous D C P compatibility h s X eta)
  change IsOpen ((fun v : Vf => eta.1 v) '' (Λf : Set Vf))
  exact he _ (harrisHodgePELIntegralAdeleSpan_isOpen D C)

private theorem compact_open_bound {V : Type*} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    (J K : AddSubgroup V) (hJ : IsCompact (J : Set V)) (hK : IsOpen (K : Set V)) :
    ∃ m : ℕ, 0 < m ∧ ∀ w : V, w ∈ J → m • w ∈ K := by
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  let U : AddSubgroup J := K.comap J.subtype
  have hU : IsOpen (U : Set J) := hK.preimage continuous_subtype_val
  let : Finite (J ⧸ U) := AddSubgroup.quotient_finite_of_isOpen U hU
  refine ⟨U.index, ?_, ?_⟩
  · change 0 < Nat.card (J ⧸ U)
    exact Nat.card_pos
  · intro w hw
    exact U.nsmul_index_mem ⟨w, hw⟩

omit [IsScalarTower ℚ F A] in
include hs htor hu in
/-- One positive integer gives both commensurability bounds with the full actual
integral Tate rationalization image, without a Tate-rank hypothesis. -/
theorem harrisIntegralFrameLattice_integerBounds (X : PObj) (eta : Frame X) :
    letI := auxiliaryStarRing D C
    ∃ m : ℕ, 0 < m ∧
      (∀ x : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
        m • GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) x ∈ lattice X eta) ∧
      (∀ w : Rat X, w ∈ lattice X eta →
        ∃ x : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
          GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
            (fun _ => True) x = m • w) := by
  let := auxiliaryStarRing D C
  let : TopologicalSpace (Rat X) := tateTopology X
  let : IsTopologicalAddGroup (Rat X) :=
    Tate.rationalFull_topologicalAddGroup X.actionObj.abelianScheme (Over.mk s)
  let I : AddSubgroup (Rat X) := (GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
    (Over.mk s) (fun _ => True)).toAddMonoidHom.range
  have hI := Tate.rationalFull_compactOpen_integral X.actionObj.abelianScheme s hs htor hu
  obtain ⟨a, ha, hlow⟩ := compact_open_bound I (lattice X eta).toAddSubgroup hI.1
    (harrisIntegralFrameLattice_isOpen D C P compatibility h s hs htor hu X eta)
  obtain ⟨b, hb, hupp⟩ := compact_open_bound (lattice X eta).toAddSubgroup I
    (harrisIntegralFrameLattice_isCompact D C P compatibility h s X eta) hI.2
  refine ⟨a * b, Nat.mul_pos ha hb, ?_, ?_⟩
  · intro x
    have hx := hlow _ (show GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
      (Over.mk s) (fun _ => True) x ∈ I from ⟨x, rfl⟩)
    have hm := (lattice X eta).toAddSubgroup.nsmul_mem hx b
    simpa only [Submodule.mem_toAddSubgroup, smul_smul, Nat.mul_comm b a] using hm
  · intro w hw
    have hx := hupp w hw
    have hm := I.nsmul_mem hx a
    change ∃ x, GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
      (fun _ => True) x = a • (b • w) at hm
    simpa only [smul_smul] using hm

variable
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "levelLattice" =>
  harrisIntegralLevelLattice D C P compatibility h s hs htor hu
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s

omit [IsScalarTower ℚ F A] in
/-- Compactness and openness belong to the carried submodule of the original level orbit. -/
theorem harrisIntegralLevelLattice_compactOpen (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) :
    letI := tateTopology X
    IsCompact (levelLattice X K hK x : Set (Rat X)) ∧
      IsOpen (levelLattice X K hK x : Set (Rat X)) := by
  let := rightAction X
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  rw [harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
    X K hK x eta heta]
  exact ⟨harrisIntegralFrameLattice_isCompact D C P compatibility h s X eta,
    harrisIntegralFrameLattice_isOpen D C P compatibility h s hs htor hu X eta⟩

omit [IsScalarTower ℚ F A] in
/-- The two integer bounds for the original fixed level orbit's carried submodule. -/
theorem harrisIntegralLevelLattice_integerBounds (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) :
    letI := auxiliaryStarRing D C
    ∃ m : ℕ, 0 < m ∧
      (∀ y : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
        m • GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) y ∈ levelLattice X K hK x) ∧
      (∀ w : Rat X, w ∈ levelLattice X K hK x →
        ∃ y : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
          GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
            (fun _ => True) y = m • w) := by
  let := auxiliaryStarRing D C
  let := rightAction X
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  rw [harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
    X K hK x eta heta]
  exact harrisIntegralFrameLattice_integerBounds D C P compatibility h s hs htor hu X eta

/-- A chosen positive common integer bound, with both proved full-integral-image
inclusions, for the submodule carried by the original fixed level orbit. -/
def harrisIntegralLevelLatticeBounds (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) :
    letI := auxiliaryStarRing D C
    { m : ℕ // 0 < m ∧
      (∀ y : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
        m • GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) y ∈ levelLattice X K hK x) ∧
      (∀ w : Rat X, w ∈ levelLattice X K hK x →
        ∃ y : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
          GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
            (fun _ => True) y = m • w) } := by
  let := auxiliaryStarRing D C
  let hm := harrisIntegralLevelLattice_integerBounds D C P compatibility h s hs htor hu X K hK x
  exact ⟨hm.choose, hm.choose_spec⟩

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
