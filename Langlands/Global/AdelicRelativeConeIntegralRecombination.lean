import Langlands.Global.AdelicRelativeSplitBaseChart
import Langlands.Global.AdelicRelativeTruncationConePartition
import Langlands.Global.AdelicOrthantPartitionIntegral

/-! # The coroot-coordinate integral of the relative cone partition -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Function
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace ArthurRelative ArthurTruncation

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)

local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "π" => levelProjection fam.connectedReductive fam.maximalSplit fam.ν D
local notation "w" => weight fam.connectedReductive fam.maximalSplit fam.ν D Δ
set_option quotPrecheck false in
local notation "Vg" => (D).realCorootSpan
local notation "C[" Q "]" => (fam.relativeSimpleRoots Q)

variable {n : ℕ}

omit [NumberField F] in
private theorem mem_outside (Q : Idx) (α : characterLattice T) : α ∈ C[Q] ↔ α ∈ Δ \ Q.val := by
  rw [relativeSimpleRoots, Finset.mem_filter, ArthurTruncation.mem_simpleFinset]
  rfl

omit [NumberField F] in
private theorem weightCoordinate_formula (Q : Idx) (Y : V T) (α : C[Q]) :
    fam.weightCoordinate Q Y α = w α.val Y := by
  have h : (simpleFinset fam.ν fam.connectedReductive fam.maximalSplit :
      Set (characterLattice T)) = Δ := Set.ext fun _ => mem_simpleFinset _ _
  unfold weightCoordinate
  rw [h]

omit [NumberField F] in
private theorem projection_mem (Q : Idx) {Y : V T} (hY : Y ∈ Vg) :
    π Q.val Y ∈ aSpace T Q.val ⊓ Vg := by
  have hspan : corootSubspace D Q.val ≤ Vg := by
    apply Submodule.span_mono
    rintro _ ⟨α, _, rfl⟩
    exact ⟨α, rfl⟩
  refine ⟨levelProjection_mem_rootAnnihilator fam.connectedReductive fam.maximalSplit D
    fam.generic Q.property Y, ?_⟩
  change π Q.val Y ∈ Vg
  have h := (Vg).sub_mem hY (hspan (sub_levelProjection_mem_span fam.connectedReductive
    fam.maximalSplit (ν := fam.ν) D Q.val Y))
  simpa only [sub_sub_cancel] using h

/-- The face coordinates indexed by the roots inside `Q` and outside `I`. -/
def relativeConeFace (coordinates : Fin n ≃ C[I]) (Q : Idx) : Set (Fin n) :=
  {a | (coordinates a).val ∈ Q.val}

local notation "Face[" E "," Q "]" => (fam.relativeConeFace I E Q)
/-- The real coordinate space complementary to the negative face. -/
abbrev RelativeConeSplitCoordinates (coords : Fin n ≃ C[I]) (Q : Idx) :=
  {a : Fin n // a ∉ fam.relativeConeFace I coords Q} → ℝ

/-- The complementary coordinates of a face are the outside roots of `Q`. -/
def relativeConeSplitIndex (coords : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) :
    Equiv {a : Fin n // a ∉ fam.relativeConeFace I coords Q} (C[Q] : Type) := by
  let fromIndex (α : C[Q]) : {a : Fin n // a ∉ fam.relativeConeFace I coords Q} := by
    have ha := (fam.mem_outside Q α.val).mp α.property
    let b : C[I] := ⟨α.val, (fam.mem_outside I _).mpr ⟨ha.1, fun h => ha.2 (hIQ h)⟩⟩
    refine ⟨coords.symm b, ?_⟩
    change (coords (coords.symm b)).val ∉ Q.val
    rw [coords.apply_symm_apply]
    exact ha.2
  refine { toFun := fun a => ⟨(coords a.val).val,
             (fam.mem_outside Q _).mpr
               ⟨((fam.mem_outside I _).mp (coords a.val).property).1, a.property⟩⟩
           invFun := fromIndex
           left_inv := ?_
           right_inv := ?_ }
  · intro a
    apply Subtype.ext
    apply coords.injective
    change coords (coords.symm _) = coords a.val
    rw [coords.apply_symm_apply]
  · intro α
    apply Subtype.ext
    change (coords (coords.symm _)).val = α.val
    rw [coords.apply_symm_apply]

private def splitCoefficients (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (y : fam.RelativeConeSplitCoordinates I e Q) : C[Q] → ℝ :=
  fun α => y ((fam.relativeConeSplitIndex I e hIQ).symm α)

private def splitDisplacement (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (Tp : V T) (y : fam.RelativeConeSplitCoordinates I e Q) : V T :=
  fam.relativeSplitVector Q (fam.splitCoefficients I e hIQ y) - π Q.val Tp

/-- The compact split base of a face, reindexed into the complementary coordinates. -/
def relativeConeFaceBase (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (Tp S : V T) : Set (fam.RelativeConeSplitCoordinates I e Q) :=
  fam.splitCoefficients I e hIQ ⁻¹' fam.relativeSplitClosedBase Q Tp S

/-- The strict split shell in the complementary coordinates. -/
def relativeConeFaceStrictBase (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q)
    (Tp S : V T) : Set (fam.RelativeConeSplitCoordinates I e Q) :=
  fam.splitCoefficients I e hIQ ⁻¹' (fam.relativeSplitVector Q ⁻¹'
    characteristicSplitShell fam.connectedReductive fam.maximalSplit D Q Tp S)

private theorem relativeConeFaceBase_ae (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q)
    {Tp S : V T} (hT : Tp ∈ Vg) : fam.relativeConeFaceStrictBase I e hIQ Tp S =ᵐ[volume]
      fam.relativeConeFaceBase I e hIQ Tp S := by
  let q := fam.relativeConeSplitIndex I e hIQ
  let f := MeasurableEquiv.piCongrLeft (fun _ : C[Q] => ℝ) q
  have hf : fam.splitCoefficients I e hIQ = f := by
    funext y a
    have ha := MeasurableEquiv.piCongrLeft_apply_apply q (β := fun _ : C[Q] => ℝ) y (q.symm a)
    rw [q.apply_symm_apply] at ha
    exact ha.symm
  have hmp : MeasurePreserving (fam.splitCoefficients I e hIQ) volume volume := by
    rw [hf]
    exact volume_measurePreserving_piCongrLeft (fun _ : C[Q] => ℝ) q
  exact hmp.quasiMeasurePreserving.ae_eq_comp ((fam.relativeSplitBaseChart Q) Tp S hT).2

/-- Placement of the split base at the vertex of the translated negative Levi face. -/
def relativeConeFacePlacement (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (Tp : V T) (y : fam.RelativeConeSplitCoordinates I e Q) (a : Fin n) : ℝ :=
  fam.weightCoordinate I (π I.val Tp + fam.splitDisplacement I e hIQ Tp y) (e a)

omit [NumberField F] in
private theorem facePlacement_continuous (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (Tp : V T) :
    Continuous (fam.relativeConeFacePlacement I e hIQ Tp) := by
  apply continuous_pi
  intro a
  let L := ((w (e a).val).comp (fam.relativeSplitVector Q)).toContinuousLinearMap
  have hL : Continuous (fam.splitCoefficients I e hIQ) :=
    continuous_pi fun j => continuous_apply ((fam.relativeConeSplitIndex I e hIQ).symm j)
  simp only [relativeConeFacePlacement, fam.weightCoordinate_formula I, splitDisplacement, map_add, map_sub]
  exact continuous_const.add ((L.continuous.comp hL).sub continuous_const)

omit [NumberField F] in
private theorem facePlacement_outside (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (Tp : V T) (y : fam.RelativeConeSplitCoordinates I e Q)
    (a : {a : Fin n // a ∉ Face[e, Q]}) : fam.relativeConeFacePlacement I e hIQ Tp y a.val = y a := by
  let α : C[Q] := fam.relativeConeSplitIndex I e hIQ a
  have ha : α.val ∈ Δ \ Q.val := (fam.mem_outside Q _).mp α.property
  have haI : α.val ∉ I.val := fun h => ha.2 (hIQ h)
  change fam.weightCoordinate I (π I.val Tp + fam.splitDisplacement I e hIQ Tp y) (e a.val) = _
  rw [fam.weightCoordinate_formula I, splitDisplacement, map_add, map_sub]
  change w α.val (π I.val Tp) +
    (w α.val (fam.relativeSplitVector Q (fam.splitCoefficients I e hIQ y)) - w α.val (π Q.val Tp)) = _
  rw [weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic I.property ha.1 haI,
    weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic Q.property ha.1 ha.2,
    ← fam.weightCoordinate_formula Q (fam.relativeSplitVector Q (fam.splitCoefficients I e hIQ y)) α,
    fam.relativeSplitVector_weight Q]
  simp only [splitCoefficients, α, Equiv.symm_apply_apply]
  ring

private theorem faceBase_compact (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) {Tp S : V T} (hT : Tp ∈ Vg) :
    IsCompact (fam.relativeConeFaceBase I e hIQ Tp S) := by
  let q := fam.relativeConeSplitIndex I e hIQ
  let L (c : C[Q] → ℝ) (a : {a : Fin n // a ∉ Face[e, Q]}) := c (q a)
  have hL : Continuous L := continuous_pi fun a => continuous_apply (q a)
  have hh := ((fam.relativeSplitBaseChart Q) Tp S hT).1.image hL
  convert hh using 1
  ext y
  constructor
  · intro hy
    refine ⟨fam.splitCoefficients I e hIQ y, hy, ?_⟩
    funext a
    change y (q.symm (q a)) = y a
    rw [q.symm_apply_apply]
  · rintro ⟨c, hc, rfl⟩
    have h : fam.splitCoefficients I e hIQ (L c) = c := by
      funext α
      change c (q (q.symm α)) = c α
      rw [q.apply_symm_apply]
    change fam.splitCoefficients I e hIQ (L c) ∈ fam.relativeSplitClosedBase Q Tp S
    rwa [h]

omit [NumberField F] in
private theorem faceBase_iff (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q) (Tp S : V T) (y : fam.RelativeConeSplitCoordinates I e Q) :
    y ∈ fam.relativeConeFaceBase I e hIQ Tp S ↔
      (∀ α ∈ Δ, 0 ≤ eval T α (fam.splitDisplacement I e hIQ Tp y)) ∧
        ∀ α ∈ Δ \ Q.val, w α (fam.splitDisplacement I e hIQ Tp y - S) ≤ 0 := by
  let y' := fam.splitCoefficients I e hIQ y
  have hzero (α : characterLattice T) (ha : α ∈ Q.val) :
      eval T α (fam.splitDisplacement I e hIQ Tp y) = 0 := by
    rw [splitDisplacement, map_sub,
      (mem_rootAnnihilator _ _).mp (fam.relativeSplitVector_mem Q y').1 α ha,
      (mem_rootAnnihilator _ _).mp (levelProjection_mem_rootAnnihilator fam.connectedReductive
        fam.maximalSplit D fam.generic Q.property Tp) α ha, sub_zero]
  have hweight (α : C[Q]) : w α.val (fam.splitDisplacement I e hIQ Tp y - S) =
      y' α - fam.weightCoordinate Q (Tp + S) α := by
    have ha := (fam.mem_outside Q _).mp α.property
    rw [splitDisplacement, map_sub, map_sub, fam.weightCoordinate_formula Q, map_add,
      weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic Q.property ha.1 ha.2,
      ← fam.weightCoordinate_formula Q _ α, fam.relativeSplitVector_weight Q]
    ring
  constructor
  · intro h
    refine ⟨fun α ha => ?_, fun α ha => ?_⟩
    · by_cases hα : α ∈ Q.val
      · rw [hzero α hα]
      · exact (h ⟨α, (fam.mem_outside Q α).mpr ⟨ha, hα⟩⟩).1
    · let a : C[Q] := ⟨α, (fam.mem_outside Q α).mpr ha⟩
      change w a.val (fam.splitDisplacement I e hIQ Tp y - S) ≤ 0
      rw [hweight a, sub_nonpos]
      exact (h a).2
  · rintro ⟨hr, hw⟩ a
    have ha := (fam.mem_outside Q _).mp a.property
    exact ⟨hr a.val ha.1, sub_nonpos.mp ((hweight a) ▸ hw a.val ha)⟩

omit [NumberField F] in
private theorem weight_nonpos_inside_of_outside {Q : Idx} {H : V T}
    (hout : ∀ β ∈ Δ \ Q.val, w β H ≤ 0)
    (hr : ∀ β ∈ Q.val, eval T β H ≤ 0) : ∀ α ∈ Q.val, w α H ≤ 0 := by
  let := finite_indivisibleRoots fam.connectedReductive fam.maximalSplit
  intro α ha
  let a : RelativeRoot.indivisibleRoots fam.i := ⟨α,
    simpleRelativeRoots_subset_indivisibleRoots fam.connectedReductive fam.maximalSplit fam.ν
      (Q.property ha)⟩
  let d := base fam.connectedReductive fam.maximalSplit fam.generic D
  have hsub : standardIndex fam.connectedReductive fam.maximalSplit fam.ν Q.val ⊆
      standardIndex fam.connectedReductive fam.maximalSplit fam.ν Δ :=
    standardIndex_mono fam.connectedReductive fam.maximalSplit fam.ν Q.property
  have ha' : a ∈ standardIndex fam.connectedReductive fam.maximalSplit fam.ν Q.val :=
    (mem_standardIndex _ _ _).mpr ⟨Q.property ha, ha⟩
  have hle : w α H ≤ weight fam.connectedReductive fam.maximalSplit fam.ν D Q.val α H := by
    rw [← neg_le_neg_iff, ← map_neg, ← map_neg, show α = a.val from rfl, weight_coe, weight_coe]
    apply ArthurCombinatorics.weightCoordinate_le_of_subset d hsub
      (standardIndex_subset_support fam.connectedReductive fam.maximalSplit D fam.generic Δ) ha'
    intro b hb
    obtain ⟨hbD, hbJ⟩ := Finset.mem_sdiff.mp hb
    have hbΔ := ((mem_standardIndex _ _ _).mp hbD).1
    rw [← weight_coe, map_neg, neg_nonneg]
    exact hout b.val ⟨hbΔ, fun hw => hbJ ((mem_standardIndex _ _ _).mpr ⟨hbΔ, hw⟩)⟩
  apply hle.trans
  rw [show α = a.val from rfl, weight_coe]
  apply ArthurCombinatorics.weightCoordinate_nonpos d
    (standardIndex_subset_support fam.connectedReductive fam.maximalSplit D fam.generic Q.val)
  intro b hb
  have h := eval_sub_toCorootSpan fam.connectedReductive fam.maximalSplit D b.property.1 H
  rw [map_sub, sub_eq_zero] at h
  calc
    _ = eval T b.val (toCorootSpan fam.connectedReductive fam.maximalSplit D H) := by
      rw [eval_eq_pair]
      rfl
    _ = eval T b.val H := h.symm
    _ ≤ 0 := hr b.val ((mem_standardIndex _ _ _).mp hb).2


private def displacement (e : Fin n ≃ C[I]) {Tp : V T} (hT : Tp ∈ Vg)
    (x : Fin n → ℝ) : Vg :=
  ⟨fam.relativeSplitVector I (fun a => x (e.symm a)) - π I.val Tp,
    (Vg).sub_mem (fam.relativeSplitVector_mem I _).2 (fam.projection_mem I hT).2⟩

omit [NumberField F] in
private theorem displacement_mem (e : Fin n ≃ C[I]) {Tp : V T} (hT : Tp ∈ Vg)
    (x : Fin n → ℝ) : (fam.displacement I e hT x : V T) ∈ aSpace T I.val :=
  (aSpace T I.val).sub_mem (fam.relativeSplitVector_mem I _).1 (fam.projection_mem I hT).1

omit [NumberField F] in
private theorem weight_displacement (e : Fin n ≃ C[I]) {Tp : V T} (hT : Tp ∈ Vg)
    (x : Fin n → ℝ) (a : Fin n) : w (e a).val (fam.displacement I e hT x) =
      x a - w (e a).val Tp := by
  have ha := (fam.mem_outside I _).mp (e a).property
  change w (e a).val (fam.relativeSplitVector I (fun b => x (e.symm b)) - π I.val Tp) = _
  rw [map_sub, weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic
    I.property ha.1 ha.2, ← fam.weightCoordinate_formula I (fam.relativeSplitVector I _) (e a),
    fam.relativeSplitVector_weight I, e.symm_apply_apply]

private theorem faceCell_iff (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q)
    {Tp S : V T} (hT : Tp ∈ Vg) (hS : S ∈ Vg) (x : Fin n → ℝ) :
    x ∈ orthantFaceCell (Face[e, Q]) (fam.relativeConeFaceBase I e hIQ Tp S)
      (fam.relativeConeFacePlacement I e hIQ Tp) ↔
    ∃ Y Z : Vg,
      IsRelativeTruncatedConeDecomposition fam.connectedReductive fam.maximalSplit D
        I Q ⟨S, hS⟩ (fam.displacement I e hT x) Y Z := by
  let y (a : {a : Fin n // a ∉ Face[e, Q]}) := x a.val
  let c := fam.splitCoefficients I e hIQ y
  let Y := fam.splitDisplacement I e hIQ Tp y
  let X := fam.displacement I e hT x
  let b := fam.relativeConeFacePlacement I e hIQ Tp
  have hY : Y ∈ aSpace T Q.val ⊓ Vg :=
    (aSpace T Q.val ⊓ Vg).sub_mem (fam.relativeSplitVector_mem Q c) (fam.projection_mem Q hT)
  have hYI : Y ∈ aSpace T I.val :=
    (mem_rootAnnihilator _ _).mpr fun α ha => (mem_rootAnnihilator _ _).mp hY.1 α (hIQ ha)
  have hweight (a : Fin n) : w (e a).val (Y - (X : V T)) = b y a - x a := by
    have ha := (fam.mem_outside I _).mp (e a).property
    rw [map_sub, fam.weight_displacement I e hT x a]
    change _ = fam.weightCoordinate I (π I.val Tp + Y) (e a) - x a
    rw [fam.weightCoordinate_formula I, map_add,
      weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic
        I.property ha.1 ha.2]
    ring
  change (y ∈ fam.relativeConeFaceBase I e hIQ Tp S ∧ (∀ a : Face[e, Q], x a.val < b y a.val)) ↔ _
  constructor
  · rintro ⟨hy, hlt⟩
    let Z : Vg := ⟨Y - (X : V T), (Vg).sub_mem hY.2 X.property⟩
    have hXI := fam.displacement_mem I e hT x
    obtain ⟨hroot, hcut⟩ := (fam.faceBase_iff I e hIQ Tp S y).mp hy
    refine ⟨⟨Y, hY.2⟩, Z, hIQ, ?_, ⟨hY.1, hroot⟩, hcut,
      (aSpace T I.val).sub_mem hYI hXI, ?_, ?_⟩
    · apply Subtype.ext
      change (X : V T) = Y - (Y - (X : V T))
      abel
    · intro α ha
      let a : Fin n := e.symm ⟨α, (fam.mem_outside I α).mpr ⟨Q.property ha.1, ha.2⟩⟩
      have hα : (e a).val = α := congrArg Subtype.val (e.apply_symm_apply _)
      have ha' : a ∈ Face[e, Q] := by
        change (e a).val ∈ Q.val
        rw [hα]
        exact ha.1
      rw [← hα]
      change 0 < w (e a).val (Y - (X : V T))
      rw [hweight, sub_pos]
      exact hlt ⟨a, ha'⟩
    · intro α ha
      let a : Fin n := e.symm ⟨α, (fam.mem_outside I α).mpr ⟨ha.1, fun h => ha.2 (hIQ h)⟩⟩
      have hα : (e a).val = α := congrArg Subtype.val (e.apply_symm_apply _)
      have ha' : a ∉ Face[e, Q] := by
        change (e a).val ∉ Q.val
        rw [hα]
        exact ha.2
      rw [← hα]
      change w (e a).val (Y - (X : V T)) = 0
      have hb : b y a = x a := fam.facePlacement_outside I e hIQ Tp y ⟨a, ha'⟩
      rw [hweight, hb, sub_self]
  · rintro ⟨Y', Z', _, hXZ, ⟨hYQ', hroot⟩, hcut, _, hpos, hzero⟩
    have hY' : (Y' : V T) + π Q.val Tp ∈ aSpace T Q.val ⊓ Vg :=
      (aSpace T Q.val ⊓ Vg).add_mem ⟨hYQ', Y'.property⟩ (fam.projection_mem Q hT)
    have hYcoord : fam.weightCoordinate Q ((Y' : V T) + π Q.val Tp) = c := by
      funext α
      let a := (fam.relativeConeSplitIndex I e hIQ).symm α
      have ha : (e a.val).val = α.val :=
        congrArg Subtype.val ((fam.relativeConeSplitIndex I e hIQ).apply_symm_apply α)
      have hα := (fam.mem_outside Q _).mp α.property
      have hsub : (X : V T) = (Y' : V T) - (Z' : V T) := congrArg Subtype.val hXZ
      have hw := fam.weight_displacement I e hT x a.val
      change w (e a.val).val (X : V T) = _ at hw
      rw [ha, hsub, map_sub, hzero α.val hα, sub_zero] at hw
      rw [fam.weightCoordinate_formula Q, map_add,
        weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic Q.property hα.1 hα.2,
        hw]
      change x a.val - w α.val Tp + w α.val Tp = x a.val
      ring
    have hYY : Y = (Y' : V T) := by
      change fam.relativeSplitVector Q c - π Q.val Tp = _
      rw [← hYcoord, fam.relativeSplitVector_weightCoordinate Q hY', add_sub_cancel_right]
    refine ⟨(fam.faceBase_iff I e hIQ Tp S y).mpr ?_, fun a => ?_⟩
    · change (∀ α ∈ Δ, 0 ≤ eval T α Y) ∧ ∀ α ∈ Δ \ Q.val, w α (Y - S) ≤ 0
      rw [hYY]
      exact ⟨hroot, hcut⟩
    · have ha : (e a.val).val ∈ Q.val \ I.val :=
        ⟨a.property, ((fam.mem_outside I _).mp (e a.val).property).2⟩
      have hp := hpos (e a.val).val ha
      have hZ : Y - (X : V T) = (Z' : V T) := by
        rw [hYY, show (X : V T) = (Y' : V T) - (Z' : V T) from congrArg Subtype.val hXZ]
        abel
      rw [← hZ, hweight, sub_pos] at hp
      exact hp


omit [NumberField F] in
private theorem cell_subset_cut (e : Fin n ≃ C[I]) {Q : Idx} (hIQ : I ≤ Q)
    {Tp S : V T} (hS : ∀ α ∈ Δ, 0 ≤ eval T α S) :
    orthantFaceCell (Face[e, Q]) (fam.relativeConeFaceBase I e hIQ Tp S)
      (fam.relativeConeFacePlacement I e hIQ Tp) ⊆
      {x | ∀ a, x a ≤ fam.weightCoordinate I (Tp + S) (e a)} := by
  intro x hx a
  let y (a : {a : Fin n // a ∉ Face[e, Q]}) := x a.val
  let Y := fam.splitDisplacement I e hIQ Tp y
  have hy : y ∈ fam.relativeConeFaceBase I e hIQ Tp S := hx.1
  have hcut := ((fam.faceBase_iff I e hIQ Tp S y).mp hy).2
  have hY : Y ∈ aSpace T Q.val :=
    (aSpace T Q.val).sub_mem (fam.relativeSplitVector_mem Q _).1
      (levelProjection_mem_rootAnnihilator fam.connectedReductive fam.maximalSplit D
        fam.generic Q.property Tp)
  have hr (β : characterLattice T) (hβ : β ∈ Q.val) : eval T β (Y - S) ≤ 0 := by
    rw [map_sub, (mem_rootAnnihilator _ _).mp hY β hβ, zero_sub, neg_nonpos]
    exact hS β (Q.property hβ)
  have ha := (fam.mem_outside I _).mp (e a).property
  have hle : w (e a).val (Y - S) ≤ 0 := by
    by_cases hin : (e a).val ∈ Q.val
    · exact fam.weight_nonpos_inside_of_outside hcut hr _ hin
    · exact hcut _ ⟨ha.1, hin⟩
  have ht : fam.relativeConeFacePlacement I e hIQ Tp y a ≤ fam.weightCoordinate I (Tp + S) (e a) := by
    unfold relativeConeFacePlacement
    change fam.weightCoordinate I (π I.val Tp + Y) (e a) ≤ _
    simp only [fam.weightCoordinate_formula I, map_add]
    rw [weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic
      I.property ha.1 ha.2, add_le_add_iff_left]
    exact sub_nonpos.mp (by simpa only [map_sub] using hle)
  by_cases hin : a ∈ Face[e, Q]
  · exact (le_of_lt (hx.2 ⟨a, hin⟩)).trans ht
  · have he : fam.relativeConeFacePlacement I e hIQ Tp y a = x a :=
      fam.facePlacement_outside I e hIQ Tp y ⟨a, hin⟩
    rwa [he] at ht

private theorem regularizedAffineFaceIntegral_strict (e : Fin n ≃ C[I]) {Q : Idx}
    (hIQ : I ≤ Q) {Tp S : V T} (hT : Tp ∈ Vg) (p : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) :
    regularizedAffineFaceIntegral
      (orthantFaceBaseMeasure (Face[e, Q]) (fam.relativeConeFaceBase I e hIQ Tp S))
      (Function.Embedding.subtype (· ∈ Face[e, Q]))
      (fun y => fam.relativeConeFacePlacement I e hIQ Tp y.val) p z =
    regularizedAffineFaceIntegral (volume.restrict (fam.relativeConeFaceStrictBase I e hIQ Tp S))
      (Function.Embedding.subtype (· ∈ Face[e, Q])) (fam.relativeConeFacePlacement I e hIQ Tp) p z := by
  rw [Measure.restrict_congr_set (fam.relativeConeFaceBase_ae I e hIQ hT)]
  let b := fam.relativeConeFacePlacement I e hIQ Tp
  let i : (Face[e, Q] : Type) ↪ Fin n := Function.Embedding.subtype (· ∈ Face[e, Q])
  let f (y : fam.RelativeConeSplitCoordinates I e Q) : ℂ :=
    Complex.exp (∑ a, z a * (b y a : ℂ)) *
      negativeOrthantRegularizedIntegral (fun j => z (i j)) (translatedFacePolynomial i p (b y))
  exact integral_subtype_comap (fam.faceBase_compact I e hIQ hT).measurableSet f

/-- Coroot-coordinate regularized integration for the decomposition in (7.26). For a
fixed starting parabolic `I`, each nested `Q` contributes the regularized integral along its
Levi face over the complementary strict split shell. -/
def RelativeConeIntegralRecombinationStatement (e : Fin n ≃ C[I]) : Prop :=
  ∀ {m : ℕ} (q : Fin m ≃ {Q : Idx // I ≤ Q}) (Tp S : V T),
    Tp ∈ Vg → S ∈ Vg → (∀ α ∈ Δ, 0 ≤ eval T α S) →
    ∀ (p : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ), (∀ a, z a ≠ 0) →
      let t := fun a => fam.weightCoordinate I (Tp + S) (e a)
      Complex.exp (∑ a, z a * (t a : ℂ)) * negativeOrthantRegularizedIntegral z (polynomialShift t p) =
        ∑ k, regularizedAffineFaceIntegral
          (volume.restrict (fam.relativeConeFaceStrictBase I e (q k).property Tp S))
          (Function.Embedding.subtype (· ∈ Face[e, (q k).val]))
          (fam.relativeConeFacePlacement I e (q k).property Tp) p z

set_option maxHeartbeats 2700000 in
/-- Transport the relative partition to the starting parabolic's projected coroot chart,
then apply the product-measure integral identity for the resulting orthant partition. -/
theorem relativeConeIntegralRecombination (e : Fin n ≃ C[I]) :
    fam.RelativeConeIntegralRecombinationStatement I e := by
  intro m q Tp S hT hS hSdom p z hz
  let t := fun a => fam.weightCoordinate I (Tp + S) (e a)
  let A : Set (Fin n → ℝ) := {x | ∀ a, x a ≤ t a}
  let s (k : Fin m) := Face[e, (q k).val]
  let base (k : Fin m) := fam.relativeConeFaceBase I e (q k).property Tp S
  let b (k : Fin m) := fam.relativeConeFacePlacement I e (q k).property Tp
  let cell (k : Fin m) := orthantFaceCell (s k) (base k) (b k)
  let : Finite (relativeWeylGroup fam.i) :=
    fam.connectedReductive.finite_relativeWeylGroup fam.i fam.maximalSplit
  obtain ⟨B, hB⟩ := (exists_relativeWeyl_realInnerProducts (i := fam.i) fam.maximalSplit.isSplitSubtorus.1).2
  have hpart (x : Fin n → ℝ) (hx : x ∈ A) : ∃! d : Idx × Vg × Vg,
      IsRelativeTruncatedConeDecomposition fam.connectedReductive fam.maximalSplit D
        I d.1 ⟨S, hS⟩ (fam.displacement I e hT x) d.2.1 d.2.2 := by
    apply (relativeTruncationConePartition fam.connectedReductive fam.maximalSplit D hB
      fam.generic I ⟨S, hS⟩ hSdom (fam.displacement I e hT x)).mp
    refine ⟨fam.displacement_mem I e hT x, fun α ha => ?_⟩
    let α' : C[I] := ⟨α, (fam.mem_outside I α).mpr ha⟩
    let a := e.symm α'
    have he : (e a).val = α := congrArg Subtype.val (e.apply_symm_apply α')
    rw [← he, map_sub, fam.weight_displacement I e hT x a, sub_sub, sub_nonpos, ← map_add]
    exact (fam.weightCoordinate_formula I (Tp + S) (e a)) ▸ hx a
  have hs (k : Fin m) : cell k ⊆ A := fam.cell_subset_cut I e (q k).property hSdom
  have hcover : A = ⋃ k, cell k := by
    ext x
    rw [mem_iUnion]
    constructor
    · intro hx
      obtain ⟨⟨Q, Y, Z⟩, h, _⟩ := hpart x hx
      let J : {Q : Idx // I ≤ Q} := ⟨Q, h.1⟩
      refine ⟨q.symm J, (fam.faceCell_iff I e (q (q.symm J)).property hT hS x).mpr ?_⟩
      refine ⟨Y, Z, ?_⟩
      rw [q.apply_symm_apply]
      exact h
    · rintro ⟨k, hk⟩
      exact hs k hk
  have hdis : Pairwise (Disjoint on cell) := by
    intro k l hkl
    apply disjoint_left.mpr
    intro x hxk hxl
    obtain ⟨Yk, Zk, hk⟩ := (fam.faceCell_iff I e (q k).property hT hS x).mp hxk
    obtain ⟨Yl, Zl, hl⟩ := (fam.faceCell_iff I e (q l).property hT hS x).mp hxl
    have he : (((q k).val, Yk, Zk) : Idx × Vg × Vg) = ((q l).val, Yl, Zl) :=
      (hpart x (hs k hxk)).unique hk hl
    exact hkl (q.injective (Subtype.ext (congrArg Prod.fst he)))
  refine (regularizedOrthantPartitionIntegral s base b t p (fun k =>
    fam.faceBase_compact I e (q k).property hT)
    (fun k => fam.facePlacement_continuous I e (q k).property Tp)
    (fun k => fam.facePlacement_outside I e (q k).property Tp) hdis hcover z hz).trans ?_
  exact Finset.sum_congr rfl fun k _ => fam.regularizedAffineFaceIntegral_strict I e (q k).property hT p z

end Langlands.Global.StandardParabolicFamily
