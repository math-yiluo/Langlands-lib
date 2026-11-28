import Langlands.Global.AdelicRelativeCorootHaar
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Global.AdelicNestedProjectedCoroots
import Langlands.Global.AdelicTruncationShellProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Compact split bases for the relative cone partition -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative
  ArthurTruncation

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q : StandardIndex F G fam.i fam.ν)

local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "R" => fam.relativeSimpleRoots Q
set_option quotPrecheck false in
local notation "VQ" => aSpace T Q.val ⊓ (D).realCorootSpan
local notation "π" => levelProjection fam.connectedReductive fam.maximalSplit fam.ν D Q.val
local notation "w" => weight fam.connectedReductive fam.maximalSplit fam.ν D Δ
local notation "B" => relativePositiveSubgroup (fam.l Q ≫ fam.p Q) (fam.a Q)

omit [NumberField F] in
private theorem relativeRoot_iff (α : characterLattice T) : α ∈ R ↔ α ∈ Δ \ Q.val := by
  rw [relativeSimpleRoots, Finset.mem_filter, ArthurTruncation.mem_simpleFinset]
  rfl

omit [NumberField F] in
private theorem weightCoordinate_eq_weight (u : V T) (α : R) : fam.weightCoordinate Q u α = w α.val u := by
  have he : (ArthurTruncation.simpleFinset fam.ν fam.connectedReductive fam.maximalSplit :
      Set (characterLattice T)) = Δ := Set.ext fun _ => ArthurTruncation.mem_simpleFinset _ _
  unfold weightCoordinate
  rw [he]

/-- Reconstruct a relative split vector from its projected simple-coroot coordinates. -/
def relativeSplitVector : (R → ℝ) →ₗ[ℝ] V T :=
  (VQ).subtype.comp (Fintype.linearCombination ℝ (fam.projectedSimpleCoroot Q))

omit [NumberField F] in
theorem relativeSplitVector_apply (y : R → ℝ) :
    fam.relativeSplitVector Q y = ∑ α, y α • (fam.projectedSimpleCoroot Q α).val := by
  simp only [relativeSplitVector, LinearMap.comp_apply, Fintype.linearCombination_apply,
    Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul]

omit [NumberField F] in
theorem relativeSplitVector_mem (y : R → ℝ) : fam.relativeSplitVector Q y ∈ VQ :=
  ((Fintype.linearCombination ℝ (fam.projectedSimpleCoroot Q)) y).property

omit [NumberField F] in
private theorem weight_projectedCoroot (α β : R) :
    w α.val (fam.projectedSimpleCoroot Q β).val = if α = β then 1 else 0 := by
  have ha := (fam.relativeRoot_iff Q α.val).mp α.property
  have hb := (fam.relativeRoot_iff Q β.val).mp β.property
  let root : relativeRoots fam.i := ⟨β.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q β⟩
  change w α.val (π ((D).realCoroot root)) = _
  rw [weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic
    Q.property ha.1 ha.2, weight_coroot fam.connectedReductive fam.maximalSplit D fam.generic
    subset_rfl ha.1 root hb.1]
  simp only [Subtype.ext_iff, root]

omit [NumberField F] in
/-- The ambient fundamental weights outside the Levi are the split coordinates. -/
theorem relativeSplitVector_weight (y : R → ℝ) (α : R) :
    fam.weightCoordinate Q (fam.relativeSplitVector Q y) α = y α := by
  rw [fam.weightCoordinate_eq_weight Q, fam.relativeSplitVector_apply Q, map_sum]
  simp only [map_smul, fam.weight_projectedCoroot Q, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Fintype.sum_ite_eq]

set_option maxHeartbeats 1700000 in
/-- Every vector in the relative split space is reconstructed by the outside weights. -/
theorem relativeSplitVector_weightCoordinate {Y : V T} (hY : Y ∈ VQ) :
    fam.relativeSplitVector Q (fam.weightCoordinate Q Y) = Y := by
  have hfinite := (standardLeviCentralDirections.1 F G fam.connectedReductive T fam.i
    fam.maximalSplit fam.ν fam.generic Q.val Q.property).2.1
  let : Module.Finite ℝ (V T) := hfinite
  let eT := (Module.finBasis ℝ (V T)).equivFun
  obtain ⟨L, hL⟩ := fam.relativePositiveLogCoordinates Q eT
  obtain ⟨e, he, _⟩ := fam.relativeCorootHaar Q
  let v : fam.relativePositiveRealChart Q eT := ⟨eT Y, Y, hY, rfl⟩
  let b := L.symm (Multiplicative.ofAdd v)
  let y := (e b).toAdd
  have hb : eT.symm (L b).toAdd.val = Y := by
    rw [show L b = Multiplicative.ofAdd v from L.apply_symm_apply _,
      show (Multiplicative.ofAdd v).toAdd.val = eT Y from rfl, eT.symm_apply_apply]
  obtain ⟨t, ht, htlog⟩ := (hL b).1
  obtain ⟨t', ht', htlog'⟩ := (he b).1
  have : IsAffineHom fam.T.X.hom := fam.maximalSplit.isSplitSubtorus.1.isAffineHom
  have : IsAffine fam.T.X.left := isAffine_of_isAffineHom fam.T.X.hom
  have hpoints : t.val = t'.val :=
    (isClosedEmbedding_map_of_isClosedSubgroup F fam.i fam.maximalSplit.isSplitSubtorus.2).injective
      (ht.symm.trans ht')
  have hvec : fam.relativeSplitVector Q y = Y := by
    apply (cocharacterFunctionalEquiv fam.maximalSplit.isSplitSubtorus.1).injective
    rw [cocharacterFunctionalEquiv_apply, cocharacterFunctionalEquiv_apply, fam.relativeSplitVector_apply Q,
      ← htlog', ← hpoints, htlog, hb]
  have hcoord : fam.weightCoordinate Q Y = y := by
    funext α
    rw [← hvec, fam.relativeSplitVector_weight Q]
  rwa [hcoord]

/-- The closed split cell in the coordinates of the roots outside the Levi. -/
def relativeSplitClosedBase (Tp S : V T) : Set (R → ℝ) :=
  {y | ∀ α : R, 0 ≤ eval T α.val (fam.relativeSplitVector Q y - π Tp) ∧
    y α ≤ fam.weightCoordinate Q (Tp + S) α}

omit [NumberField F] in
private theorem weight_nonneg {x : V T} (hx : ∀ α ∈ Δ, 0 ≤ eval T α x) (α : R) :
    0 ≤ w α.val x := by
  let := finite_indivisibleRoots fam.connectedReductive fam.maximalSplit
  let a : RelativeRoot.indivisibleRoots fam.i := ⟨α.val,
    simpleRelativeRoots_subset_indivisibleRoots fam.connectedReductive fam.maximalSplit fam.ν
      ((fam.relativeRoot_iff Q α.val).mp α.property).1⟩
  rw [← neg_nonpos, ← map_neg, show α.val = a.val from rfl, weight_coe]
  apply ArthurCombinatorics.weightCoordinate_nonpos
    (base fam.connectedReductive fam.maximalSplit fam.generic D)
    (standardIndex_subset_support fam.connectedReductive fam.maximalSplit D fam.generic Δ)
  intro β hβ
  have he := eval_sub_toCorootSpan fam.connectedReductive fam.maximalSplit D β.2.1 (-x)
  rw [map_sub, sub_eq_zero] at he
  calc
    _ = eval T β.1 (toCorootSpan fam.connectedReductive fam.maximalSplit D (-x)) := by
      rw [eval_eq_pair]
      rfl
    _ = eval T β.1 (-x) := he.symm
    _ ≤ 0 := by
      rw [map_neg, neg_nonpos]
      exact hx β.1 ((mem_standardIndex fam.connectedReductive fam.maximalSplit fam.ν).mp hβ).2

omit [NumberField F] in
private theorem closedBase_compact (Tp S : V T) : IsCompact (fam.relativeSplitClosedBase Q Tp S) := by
  have hclosed : IsClosed (fam.relativeSplitClosedBase Q Tp S) := by
    rw [show fam.relativeSplitClosedBase Q Tp S =
      ⋂ α : R, {y | 0 ≤ eval T α.val (fam.relativeSplitVector Q y - π Tp) ∧
        y α ≤ fam.weightCoordinate Q (Tp + S) α} by ext y; simp [relativeSplitClosedBase]]
    apply isClosed_iInter
    intro α
    let L := ((eval T α.val).comp (fam.relativeSplitVector Q)).toContinuousLinearMap
    have hL : Continuous fun y => eval T α.val (fam.relativeSplitVector Q y - π Tp) := by
      simp only [map_sub]
      exact L.continuous.sub continuous_const
    exact (isClosed_le continuous_const hL).inter (isClosed_le (continuous_apply α) continuous_const)
  refine (isCompact_Icc (a := fam.weightCoordinate Q Tp) (b := fam.weightCoordinate Q (Tp + S))).of_isClosed_subset hclosed ?_
  intro y hy
  refine ⟨fun α => ?_, fun α => (hy α).2⟩
  have hroot (β : characterLattice T) (hβ : β ∈ Δ) :
      0 ≤ eval T β (fam.relativeSplitVector Q y - π Tp) := by
    by_cases h : β ∈ Q.val
    · have hspan := (fam.relativeSplitVector_mem Q y).1
      have hπ := levelProjection_mem_rootAnnihilator fam.connectedReductive fam.maximalSplit D
        fam.generic Q.property Tp
      rw [map_sub, (mem_rootAnnihilator _ _).mp hspan β h,
        (mem_rootAnnihilator _ _).mp hπ β h, sub_zero]
    · exact (hy ⟨β, (fam.relativeRoot_iff Q β).mpr ⟨hβ, h⟩⟩).1
  have h := fam.weight_nonneg Q hroot α
  have ha := (fam.relativeRoot_iff Q α.val).mp α.property
  rw [map_sub, weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D
    fam.generic Q.property ha.1 ha.2, sub_nonneg,
    ← fam.weightCoordinate_eq_weight Q (fam.relativeSplitVector Q y) α,
    fam.relativeSplitVector_weight Q, ← fam.weightCoordinate_eq_weight Q Tp α] at h
  exact h

/-- A nonstrict split base is compact. Requiring the root bounds to be strict removes only
null walls in the relative split coordinates. -/
def RelativeSplitBaseChartStatement : Prop :=
  ∀ Tp S : V T, Tp ∈ (D).realCorootSpan →
    IsCompact (fam.relativeSplitClosedBase Q Tp S) ∧
    (fam.relativeSplitVector Q ⁻¹' characteristicSplitShell fam.connectedReductive
      fam.maximalSplit D Q Tp S) =ᵐ[volume] fam.relativeSplitClosedBase Q Tp S

set_option maxHeartbeats 2100000 in
/-- Use a standard cocharacter to witness the nonzero root functionals on the split chart. -/
theorem relativeSplitBaseChart : fam.RelativeSplitBaseChartStatement Q := by
  intro Tp S hT
  refine ⟨fam.closedBase_compact Q Tp S, ?_⟩
  have hspan : corootSubspace D Q.val ≤ (D).realCorootSpan := by
    apply Submodule.span_mono
    rintro _ ⟨β, _, rfl⟩
    exact ⟨β, rfl⟩
  have hπ : π Tp ∈ VQ := by
    refine ⟨levelProjection_mem_rootAnnihilator fam.connectedReductive fam.maximalSplit D
      fam.generic Q.property Tp, ?_⟩
    have h := (D).realCorootSpan.sub_mem hT (hspan
      (sub_levelProjection_mem_span fam.connectedReductive fam.maximalSplit (ν := fam.ν) D Q.val Tp))
    change π Tp ∈ (D).realCorootSpan
    simpa only [sub_sub_cancel] using h
  let y₀ := fam.weightCoordinate Q (π Tp)
  have hzero : fam.relativeSplitVector Q y₀ = π Tp := fam.relativeSplitVector_weightCoordinate Q hπ
  obtain ⟨⟨ζ, hζ⟩, _⟩ := standardCocharacter F G fam.connectedReductive T fam.i fam.maximalSplit
    fam.ν fam.generic Q.val Q.property
  let u := ((1 : ℝ) ⊗ₜ[ℤ] ζ : V T)
  let Z := toCorootSpan fam.connectedReductive fam.maximalSplit D u
  have hZ (β : relativeRoots fam.i) : eval T β.val Z = eval T β.val u := by
    have h := eval_sub_toCorootSpan fam.connectedReductive fam.maximalSplit D β.property u
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  have hZmem : (Z : V T) ∈ VQ := by
    refine ⟨(mem_rootAnnihilator Q.val (Z : V T)).mpr fun β hb => ?_, Z.property⟩
    let root : relativeRoots fam.i := ⟨β, simpleRelativeRoots_subset_relativeRoots fam.i fam.ν (Q.property hb)⟩
    change eval T root.val Z = 0
    rw [hZ root]
    simp [u, eval_tmul, root, hζ.2.1 β hb]
  let y₁ := fam.weightCoordinate Q (Z : V T)
  have h1 : fam.relativeSplitVector Q y₁ = (Z : V T) := fam.relativeSplitVector_weightCoordinate Q hZmem
  have hne : ∀ᵐ y : R → ℝ ∂volume, ∀ α : R,
      eval T α.val (fam.relativeSplitVector Q y - π Tp) ≠ 0 := by
    rw [ae_all_iff]
    intro α
    let L := (eval T α.val).comp (fam.relativeSplitVector Q)
    let root : relativeRoots fam.i := ⟨α.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩
    have hpos : 0 < L y₁ := by
      change 0 < eval T root.val (fam.relativeSplitVector Q y₁)
      rw [h1, hZ root]
      have ha := (fam.relativeRoot_iff Q α.val).mp α.property
      simpa [u, eval_tmul, root] using hζ.2.2 α.val ha.1 ha.2
    have hnull : (volume : Measure (R → ℝ)) (L.ker : Set (R → ℝ)) = 0 := by
      apply Measure.addHaar_submodule
      intro htop
      have hy : y₁ ∈ L.ker := htop ▸ (Submodule.mem_top : y₁ ∈ (⊤ : Submodule ℝ (R → ℝ)))
      exact hpos.ne' (LinearMap.mem_ker.mp hy)
    have hae : ∀ᵐ y : R → ℝ ∂volume, L y ≠ 0 := by
      rw [ae_iff]
      rw [show {y : R → ℝ | ¬ L y ≠ 0} = (L.ker : Set (R → ℝ)) by
        ext y
        simp [LinearMap.mem_ker]]
      exact hnull
    have ht := (measurePreserving_add_right volume (-y₀)).quasiMeasurePreserving.ae hae
    refine ht.mono fun y hy => ?_
    change L (y + -y₀) ≠ 0 at hy
    rwa [← hzero, ← map_sub, sub_eq_add_neg] 
  filter_upwards [hne] with y hy
  have hw (α : R) : w α.val (fam.relativeSplitVector Q y - π (Tp + S)) ≤ 0 ↔
      y α ≤ fam.weightCoordinate Q (Tp + S) α := by
    have ha := (fam.relativeRoot_iff Q α.val).mp α.property
    rw [map_sub, weight_levelProjection_outside fam.connectedReductive fam.maximalSplit D fam.generic
      Q.property ha.1 ha.2, sub_nonpos, ← fam.weightCoordinate_eq_weight Q,
      fam.relativeSplitVector_weight Q, ← fam.weightCoordinate_eq_weight Q]
  let hyR := fam.relativeSplitVector_mem Q y
  change (((fam.relativeSplitVector Q y ∈ (D).realCorootSpan ∧ fam.relativeSplitVector Q y ∈ aSpace T Q.val ∧
      ∀ α ∈ Δ \ Q.val, 0 < eval T α (fam.relativeSplitVector Q y - π Tp)) ∧
      (∀ α ∈ Δ \ Q.val, w α (fam.relativeSplitVector Q y - π (Tp + S)) ≤ 0)) = _)
  apply propext
  constructor
  · intro hs α
    have ha := (fam.relativeRoot_iff Q α.val).mp α.property
    exact ⟨(hs.1.2.2 α.val ha).le, (hw α).mp (hs.2 α.val ha)⟩
  · intro hs
    refine ⟨⟨hyR.2, hyR.1, fun α ha => ?_⟩, fun α ha => ?_⟩
    · let a : R := ⟨α, (fam.relativeRoot_iff Q α).mpr ha⟩
      exact lt_of_le_of_ne (hs a).1 (Ne.symm (hy a))
    · let a : R := ⟨α, (fam.relativeRoot_iff Q α).mpr ha⟩
      exact (hw a).mpr (hs a).2

end Langlands.Global.StandardParabolicFamily
