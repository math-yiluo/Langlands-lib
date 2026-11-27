import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellCutoff
import Langlands.Global.Factors.CuspidalPairEisensteinOneplaceIntegrand

/-! # Cutting a section off to the open cell at finitely many places

For a finite set `S₀` of finite places and nonzero `ε_v` with `|ε_v|_v ≤ 1`, the cutoff `β`
is the indicator of the set of `g ∈ GL_(r+t+2)(𝔸)` whose component `g_v` lies, for every
`v ∈ S₀`, in the open Bruhat cell `P_v w U'_v` with open-cell coordinate of valuation
`< |ε_v|_v`. It is left invariant under the upper two-block parabolic `P(𝔸)`, right invariant
under an open subgroup, independent of the archimedean component, and at `w u'(Y)` it is the
indicator of `|Y_v|_v < |ε_v|_v` for `v ∈ S₀`. Multiplying a section by `β` gives a section,
built from cusp forms spherical outside `S₀` when the section is built from cusp forms
spherical outside a subset of `S₀`, and multiplies the open-cell integrand at `Y` by
`β(w u'(Y))`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein.SemilocalCutoff

open scoped _root_.Topology
open NumberField Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight OpenCellCutoff Oneplace OpenCellExhaustion

section ValuedTopology

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

/-- The open ball `{x | |x| < |a|}` of a valued field is open. -/
theorem isOpen_lt_valuation (a : K) : IsOpen {x : K | hv.v x < hv.v a} := by
  have h : IsOpen {x : K | hv.v.restrict x < hv.v.restrict a} := Valued.isOpen_ball K _
  have e : {x : K | hv.v.restrict x < hv.v.restrict a} = {x : K | hv.v x < hv.v a} := by
    ext x
    exact Valuation.restrict_lt_iff _
  rwa [e] at h

/-- Every neighbourhood of `0` in a valued field contains a ball `{x | |x| < |a|}` with
`a ≠ 0` and `|a| ≤ 1`. -/
theorem exists_ball_subset {s : Set K} (hs : s ∈ 𝓝 (0 : K)) :
    ∃ a : K, a ≠ 0 ∧ hv.v a ≤ 1 ∧ {x | hv.v x < hv.v a} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  obtain ⟨a, ha⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (hv.v : K →*₀ Γ₀) γ.1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact γ.ne_zero ha.symm
  have hsub : {x | hv.v x < hv.v a} ⊆ s := by
    intro x hx
    apply hγ
    change hv.v.restrict x < γ.1
    rw [← ha, ← Valuation.restrict_def]
    exact (Valuation.restrict_lt_iff _).mpr hx
  by_cases h1 : hv.v a ≤ 1
  · exact ⟨a, ha0, h1, hsub⟩
  · refine ⟨1, one_ne_zero, le_of_eq (map_one _), fun x hx => hsub ?_⟩
    rw [Set.mem_ofPred_eq, map_one] at hx
    exact lt_trans hx (lt_of_not_ge h1)

/-- A finite product of neighbourhood bases of balls: every neighbourhood of `0` in a finite
product contains the set of points all of whose coordinates lie in a common ball. -/
theorem exists_ball_subset_pi {ι : Type*} [Fintype ι] {Y : Type*} [TopologicalSpace Y] [Zero Y]
    (B : K → Set Y) (hB : ∀ s ∈ 𝓝 (0 : Y), ∃ a : K, a ≠ 0 ∧ hv.v a ≤ 1 ∧ B a ⊆ s)
    (hmono : ∀ a b : K, hv.v a ≤ hv.v b → B a ⊆ B b) {s : Set (ι → Y)}
    (hs : s ∈ 𝓝 (0 : ι → Y)) :
    ∃ a : K, a ≠ 0 ∧ hv.v a ≤ 1 ∧ {y : ι → Y | ∀ i, y i ∈ B a} ⊆ s := by
  classical
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, u, hu, hIs⟩ := hs
  choose c hc0 hc1 hcs using fun i => hB (u i) (hu i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i, ?_, fun y hy => hIs ?_⟩
  · rw [map_prod]
    exact Finset.prod_le_one fun i _ => hc1 i
  · intro i _
    refine hcs i (hmono _ _ ?_ (hy i))
    rw [map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    exact mul_le_of_le_one_right' (Finset.prod_le_one fun j _ => hc1 j)

/-- Every neighbourhood of `0` in a matrix space over a valued field contains the matrices
with entries in a ball `{x | |x| < |a|}`, `a ≠ 0`, `|a| ≤ 1`. -/
theorem exists_matrix_ball_subset {m n : Type*} [Fintype m] [Fintype n]
    {s : Set (Matrix m n K)} (hs : s ∈ 𝓝 (0 : Matrix m n K)) :
    ∃ a : K, a ≠ 0 ∧ hv.v a ≤ 1 ∧ {y : Matrix m n K | ∀ i j, hv.v (y i j) < hv.v a} ⊆ s :=
  exists_ball_subset_pi (fun a => {y : n → K | ∀ j, hv.v (y j) < hv.v a})
    (fun _ hs' => exists_ball_subset_pi (fun a => {x : K | hv.v x < hv.v a})
      (fun _ hs'' => exists_ball_subset hs'') (fun _ _ hab _ hx => lt_of_lt_of_le hx hab) hs')
    (fun _ _ hab _ hy j => lt_of_lt_of_le (hy j) hab) hs

end ValuedTopology

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

/-- The lower left block of a matrix of the upper two-block parabolic vanishes. -/
theorem parabolic_lowerZero {R : Type*} [CommRing R] {p : Langlands.GeneralLinear (r + t + 2) R}
    (hp : p ∈ (blockShape r t).parabolic R) (i : Fin (t + 1)) (j : Fin (r + 1)) :
    (p : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) (botIdx r t i) (topIdx r t j) = 0 := by
  rw [GeneralLinear.BlockShape.mem_parabolic_iff] at hp
  have h := hp (1 : Fin 2) (0 : Fin 2) i j (by change (0 : Fin 2) < 1; decide)
  have e1 : (blockShape r t).index (1 : Fin 2) i = botIdx r t i := by
    apply Fin.ext
    change ((blockShape r t).indexEquiv ⟨(1 : Fin 2), i⟩).val = r + 1 + i.val
    rw [GeneralLinear.BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSigmaFinEquiv_apply]
    change (∑ k : Fin 1, ![r + 1, t + 1] (Fin.castLE (by decide : 1 ≤ 2) k)) + i.val =
      r + 1 + i.val
    rw [Fin.sum_univ_one]
    rfl
  have e0 : (blockShape r t).index (0 : Fin 2) j = topIdx r t j := by
    apply Fin.ext
    change ((blockShape r t).indexEquiv ⟨(0 : Fin 2), j⟩).val = j.val
    rw [GeneralLinear.BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSigmaFinEquiv_apply]
    simp
  rw [e1, e0] at h
  exact h

section Cutoff

variable (r t) in
/-- The open-cell condition at the places of `S₀`: for every `v ∈ S₀`, the component `g_v` has
invertible block `A(g_v)` and open-cell coordinate `A(g_v)⁻¹ B(g_v)` with entries of valuation
`< |ε_v|_v`. -/
def InCellAt (S₀ : Finset (FinitePlace F)) (ε : ∀ v : FinitePlace F, FiniteCompletion F v)
    (g : AdelicGL F (r + t + 2)) : Prop :=
  ∀ v ∈ S₀, InCell (Valued.v (R := FiniteCompletion F v)) r t (Valued.v (ε v))
    (comp F (r + t + 2) v g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (FiniteCompletion F v))

variable (r t) in
open Classical in
/-- The cutoff `β_(S₀, ε)`: the indicator of `InCellAt r t S₀ ε`. -/
def cutoff (S₀ : Finset (FinitePlace F)) (ε : ∀ v : FinitePlace F, FiniteCompletion F v)
    (g : AdelicGL F (r + t + 2)) : ℂ :=
  if InCellAt r t S₀ ε g then 1 else 0

variable (r t) in
/-- The right stabilizer of the open-cell condition at the places of `S₀`. -/
def stab (S₀ : Finset (FinitePlace F)) (ε : ∀ v : FinitePlace F, FiniteCompletion F v) :
    Subgroup (AdelicGL F (r + t + 2)) where
  carrier := {k | ∀ g, InCellAt r t S₀ ε (g * k) ↔ InCellAt r t S₀ ε g}
  mul_mem' {k k'} hk hk' g := by
    change InCellAt r t S₀ ε (g * (k * k')) ↔ _
    rw [← mul_assoc, hk' (g * k), hk g]
  one_mem' g := by
    rw [mul_one]
  inv_mem' {k} hk g := by
    change InCellAt r t S₀ ε (g * k⁻¹) ↔ _
    rw [← hk (g * k⁻¹), inv_mul_cancel_right]

theorem cutoff_eq_of_iff {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}
    {g g' : AdelicGL F (r + t + 2)} (h : InCellAt r t S₀ ε g' ↔ InCellAt r t S₀ ε g) :
    cutoff r t S₀ ε g' = cutoff r t S₀ ε g := by
  unfold cutoff
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.mp h1) h2
  · exact absurd (h.mpr h2) h1
  · rfl

theorem cutoff_mul_stab {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}
    {k : AdelicGL F (r + t + 2)} (hk : k ∈ stab r t S₀ ε) (g : AdelicGL F (r + t + 2)) :
    cutoff r t S₀ ε (g * k) = cutoff r t S₀ ε g :=
  cutoff_eq_of_iff (hk g)

/-- The set of local matrices congruent to `1` modulo `ε` together with their inverses. -/
def congruenceSet (v : FinitePlace F) (n : ℕ) (ε : FiniteCompletion F v) :
    Set (FiniteLocalGL F n v) :=
  {x | (∀ a b, Valued.v ((x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
      (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε) ∧
    ∀ a b, Valued.v (((x⁻¹ : FiniteLocalGL F n v) : Matrix (Fin n) (Fin n) (FiniteCompletion F v))
      a b - (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε}

theorem isOpen_congruenceSet (v : FinitePlace F) (n : ℕ) (ε : FiniteCompletion F v) :
    IsOpen (congruenceSet v n ε) := by
  have h1 : ∀ a b : Fin n, IsOpen {x : FiniteLocalGL F n v |
      Valued.v ((x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
        (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε} := fun a b => by
    have hc : Continuous fun x : FiniteLocalGL F n v =>
        (x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
          (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b :=
      (Units.continuous_val.matrix_elem a b).sub continuous_const
    exact (isOpen_lt_valuation ε).preimage hc
  have h2 : ∀ a b : Fin n, IsOpen {x : FiniteLocalGL F n v |
      Valued.v (((x⁻¹ : FiniteLocalGL F n v) : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
        (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε} := fun a b => by
    have hc : Continuous fun x : FiniteLocalGL F n v =>
        ((x⁻¹ : FiniteLocalGL F n v) : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
          (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b :=
      (Units.continuous_coe_inv.matrix_elem a b).sub continuous_const
    exact (isOpen_lt_valuation ε).preimage hc
  have e : congruenceSet v n ε = (⋂ a, ⋂ b, {x : FiniteLocalGL F n v |
      Valued.v ((x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
        (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε}) ∩
      ⋂ a, ⋂ b, {x : FiniteLocalGL F n v |
      Valued.v (((x⁻¹ : FiniteLocalGL F n v) : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
        (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε} := by
    ext x
    simp only [congruenceSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => h1 a b).inter
    (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => h2 a b)

theorem one_mem_congruenceSet (v : FinitePlace F) (n : ℕ) {ε : FiniteCompletion F v}
    (hε : ε ≠ 0) : (1 : FiniteLocalGL F n v) ∈ congruenceSet v n ε := by
  have h : ∀ a b : Fin n, Valued.v (((1 : FiniteLocalGL F n v) :
      Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b -
        (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) a b) < Valued.v ε := by
    intro a b
    rw [Units.val_one, sub_self, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hε)
  refine ⟨h, ?_⟩
  rw [inv_one]
  exact h

/-- Right multiplication by an element of the congruence set preserves the open-cell
condition, in both directions. -/
theorem inCell_mul_iff_of_mem {v : FinitePlace F} {ε : FiniteCompletion F v} (hε0 : ε ≠ 0)
    (hε1 : Valued.v ε ≤ 1) (X : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (FiniteCompletion F v))
    {y : FiniteLocalGL F (r + t + 2) v} (hy : y ∈ congruenceSet v (r + t + 2) ε) :
    InCell Valued.v r t (Valued.v ε)
        (X * (y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (FiniteCompletion F v))) ↔
      InCell Valued.v r t (Valued.v ε) X := by
  have hγ0 : Valued.v ε ≠ 0 := (Valuation.ne_zero_iff _).mpr hε0
  constructor
  · intro h
    have h' := InCell.mul_right hγ0 hε1 hy.2 h
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h'
  · exact InCell.mul_right hγ0 hε1 hy.1

theorem continuous_comp (n : ℕ) (v : FinitePlace F) : Continuous (comp F n v) :=
  (FiniteAdelicGL.localProjection F n v).continuous.comp (AdelicGL.finite F n).continuous

/-- The stabilizer of the open-cell condition is open. -/
theorem isOpen_stab {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}
    (hε : ∀ v ∈ S₀, ε v ≠ 0 ∧ Valued.v (ε v) ≤ 1) :
    IsOpen (stab r t S₀ ε : Set (AdelicGL F (r + t + 2))) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hW : (⋂ v ∈ S₀, comp F (r + t + 2) v ⁻¹' congruenceSet v (r + t + 2) (ε v)) ∈
      𝓝 (1 : AdelicGL F (r + t + 2)) := by
    refine (Filter.biInter_finset_mem S₀).mpr fun v hv => ?_
    refine (continuous_comp (r + t + 2) v).continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact (isOpen_congruenceSet v _ (ε v)).mem_nhds (one_mem_congruenceSet v _ (hε v hv).1)
  refine Filter.mem_of_superset hW fun k hk g => ?_
  simp only [Set.mem_iInter, Set.mem_preimage] at hk
  refine forall₂_congr fun v hv => ?_
  rw [map_mul, Units.val_mul]
  exact inCell_mul_iff_of_mem (hε v hv).1 (hε v hv).2 _ (hk v hv)

/-- The stabilizer as an open subgroup. -/
def openStab {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}
    (hε : ∀ v ∈ S₀, ε v ≠ 0 ∧ Valued.v (ε v) ≤ 1) : OpenSubgroup (AdelicGL F (r + t + 2)) :=
  ⟨stab r t S₀ ε, isOpen_stab hε⟩

/-- The cutoff is left invariant under the upper two-block parabolic. -/
theorem cutoff_mul_left {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}
    {p : AdelicGL F (r + t + 2)} (hp : p ∈ (blockShape r t).parabolic (Adeles F))
    (g : AdelicGL F (r + t + 2)) : cutoff r t S₀ ε (p * g) = cutoff r t S₀ ε g := by
  refine cutoff_eq_of_iff (forall₂_congr fun v _ => ?_)
  have hz : ∀ i j, (comp F (r + t + 2) v p :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (FiniteCompletion F v)) (botIdx r t i)
        (topIdx r t j) = 0 := by
    intro i j
    rw [comp_apply, parabolic_lowerZero hp i j]
    rfl
  have hpq : (comp F (r + t + 2) v p :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (FiniteCompletion F v)) *
      (comp F (r + t + 2) v p⁻¹ : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (FiniteCompletion F v))
        = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [map_mul, Units.val_mul]
  exact inCell_mul_left_iff hz hpq

/-- At `w u'(Y)` the cutoff is the indicator of `|Y_v| < |ε_v|_v` for `v ∈ S₀`. -/
theorem inCellAt_openCell_iff (S₀ : Finset (FinitePlace F))
    (ε : ∀ v : FinitePlace F, FiniteCompletion F v)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    InCellAt r t S₀ ε (openCellWeyl F r t * openCellUnipotent F r t Y) ↔
      ∀ v ∈ S₀, ∀ i j, Valued.v (matrixComponent v Y i j) < Valued.v (ε v) := by
  refine forall₂_congr fun v _ => ?_
  have e : comp F (r + t + 2) v (openCellWeyl F r t * openCellUnipotent F r t Y) =
      openCellMatrix (matrixComponent v Y) := by
    rw [map_mul, comp_openCellWeyl, comp_openCellUnipotent, ← map_mul]
  rw [e]
  exact inCell_openCellMatrix_iff _ _ _

/-- The cutoff is right invariant under matrices supported at a place outside `S₀`. -/
theorem cutoff_mul_adelicAt {S₀ : Finset (FinitePlace F)}
    {ε : ∀ v : FinitePlace F, FiniteCompletion F v} {v : FinitePlace F} (hv : v ∉ S₀)
    (k : FiniteLocalGL F (r + t + 2) v) (g : AdelicGL F (r + t + 2)) :
    cutoff r t S₀ ε (g * adelicAt F (r + t + 2) v k) = cutoff r t S₀ ε g := by
  refine cutoff_eq_of_iff (forall₂_congr fun w hw => ?_)
  have hwv : w ≠ v := fun h => hv (h ▸ hw)
  rw [map_mul, comp_adelicAt_of_ne _ hwv, mul_one]

/-- The cutoff does not depend on the archimedean component. -/
theorem cutoff_pair {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}
    (a : InfiniteAdelicGL F (r + t + 2)) (b : FiniteAdelicGL F (r + t + 2)) :
    cutoff r t S₀ ε (AdelicGL.pair F (r + t + 2) a b) =
      cutoff r t S₀ ε (AdelicGL.pair F (r + t + 2) 1 b) := by
  refine cutoff_eq_of_iff (forall₂_congr fun v _ => ?_)
  have e : ∀ c : InfiniteAdelicGL F (r + t + 2),
      comp F (r + t + 2) v (AdelicGL.pair F (r + t + 2) c b) =
        FiniteAdelicGL.localProjection F (r + t + 2) v b := by
    intro c
    change FiniteAdelicGL.localProjection F (r + t + 2) v
      (AdelicGL.finite F (r + t + 2) (AdelicGL.pair F (r + t + 2) c b)) = _
    rw [AdelicGL.finite_pair]
  rw [e, e]

end Cutoff

section Section

variable {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}

theorem leviEmbedding_mem_parabolic (m : FullLevi F (blockShape r t)) :
    (blockShape r t).leviEmbedding (Adeles F) m ∈ (blockShape r t).parabolic (Adeles F) :=
  ((blockShape r t).leviInParabolic (Adeles F) m).property

theorem unipotent_mem_parabolic (n : (blockShape r t).unipotentSubgroup (Adeles F)) :
    n.val ∈ (blockShape r t).parabolic (Adeles F) :=
  ((GeneralLinear.BlockShape.mem_unipotentSubgroup_iff _ _ _).mp n.property).1

/-- The right translates of the cutoff by the standard compact subgroup form a finite set. -/
theorem finite_range_cutoff_translate (hε : ∀ v ∈ S₀, ε v ≠ 0 ∧ Valued.v (ε v) ≤ 1) :
    (Set.range fun k : standardCompact F (r + t + 2) =>
      fun g : AdelicGL F (r + t + 2) => cutoff r t S₀ ε (g * k.val)).Finite := by
  let K := standardCompact F (r + t + 2)
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_standardCompact F _)
  let H : Subgroup K := (stab r t S₀ ε).comap K.subtype
  have hH : IsOpen (H : Set K) := (isOpen_stab hε).preimage continuous_subtype_val
  have : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  let b : K ⧸ H → AdelicGL F (r + t + 2) → ℂ :=
    Quotient.lift (fun k : K => fun g : AdelicGL F (r + t + 2) => cutoff r t S₀ ε (g * k.val))
      (fun k k' hkk' => by
        funext g
        have hmem : k⁻¹ * k' ∈ H := QuotientGroup.leftRel_apply.mp hkk'
        have e : k'.val = k.val * (k⁻¹ * k').val := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
        change cutoff r t S₀ ε (g * k.val) = cutoff r t S₀ ε (g * k'.val)
        rw [e, ← mul_assoc]
        exact (cutoff_mul_stab (show ((k⁻¹ * k' : K) : AdelicGL F (r + t + 2)) ∈
          stab r t S₀ ε from hmem) (g * k.val)).symm)
  refine (Set.finite_range b).subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨QuotientGroup.mk k, rfl⟩

/-- The normalized Levi slice of `β φ` at `k` is `β(k)` times that of `φ`, since `β` is left
invariant under the Levi. -/
theorem slice_cutoff_mul_mem {φ : AdelicGL F (r + t + 2) → ℂ} {k : AdelicGL F (r + t + 2)}
    {M : Submodule ℂ (FullLevi F (blockShape r t) → ℂ)}
    (h : (fun m : FullLevi F (blockShape r t) =>
      ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        φ ((blockShape r t).leviEmbedding (Adeles F) m * k)) ∈ M) :
    (fun m : FullLevi F (blockShape r t) =>
      ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        (cutoff r t S₀ ε ((blockShape r t).leviEmbedding (Adeles F) m * k) *
          φ ((blockShape r t).leviEmbedding (Adeles F) m * k))) ∈ M := by
  have e : (fun m : FullLevi F (blockShape r t) =>
      ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        (cutoff r t S₀ ε ((blockShape r t).leviEmbedding (Adeles F) m * k) *
          φ ((blockShape r t).leviEmbedding (Adeles F) m * k))) =
      cutoff r t S₀ ε k • (fun m : FullLevi F (blockShape r t) =>
        ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
          φ ((blockShape r t).leviEmbedding (Adeles F) m * k)) := by
    funext m
    rw [cutoff_mul_left (leviEmbedding_mem_parabolic m), Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact M.smul_mem _ h

variable [CompactSpace (AdeleQuotient F)] {T : CuspidalOperatorRealization F r}
  {T' : CuspidalOperatorRealization F t}

/-- Multiplying a section by the cutoff gives a section. -/
theorem isSection_cutoff_mul (hε : ∀ v ∈ S₀, ε v ≠ 0 ∧ Valued.v (ε v) ≤ 1)
    {φ : AdelicGL F (r + t + 2) → ℂ} (hφ : IsSection T T' φ) :
    IsSection T T' (fun g => cutoff r t S₀ ε g * φ g) := by
  obtain ⟨hsmooth, ⟨J, hJ⟩, hfin, hunip, hslice⟩ := hφ
  refine ⟨fun b => ?_, ?_, ?_, fun n g => ?_, fun k => ?_⟩
  · have e : (fun a => cutoff r t S₀ ε (AdelicGL.pair F (r + t + 2) a b) *
        φ (AdelicGL.pair F (r + t + 2) a b)) =
        cutoff r t S₀ ε (AdelicGL.pair F (r + t + 2) 1 b) •
          (fun a => φ (AdelicGL.pair F (r + t + 2) a b)) := by
      funext a
      rw [cutoff_pair, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (hsmooth b)
  · refine ⟨J ⊓ (openStab (r := r) (t := t) hε).comap (AdelicGL.ofFinite F (r + t + 2)).toMonoidHom
      (AdelicGL.ofFinite F (r + t + 2)).continuous, fun j g => ?_⟩
    have h1 : j.val ∈ J := j.property.1
    have h2 : AdelicGL.ofFinite F (r + t + 2) j.val ∈ stab r t S₀ ε := j.property.2
    change cutoff r t S₀ ε (g * AdelicGL.ofFinite F (r + t + 2) j.val) *
        φ (g * AdelicGL.ofFinite F (r + t + 2) j.val) = cutoff r t S₀ ε g * φ g
    rw [cutoff_mul_stab h2, hJ ⟨j.val, h1⟩ g]
  · classical
    let V := Submodule.span ℂ (Set.range
      (fun k : standardCompact F (r + t + 2) => fun g => φ (g * k.val)))
    have : FiniteDimensional ℂ V := hfin
    obtain ⟨B, hB⟩ := (finite_range_cutoff_translate (r := r) (t := t) hε).exists_finset_coe
    let W := B.sup fun b => V.map (LinearMap.mulLeft ℂ b)
    have : FiniteDimensional ℂ W := by
      dsimp only [W]
      infer_instance
    refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    have hk : (fun g : AdelicGL F (r + t + 2) => cutoff r t S₀ ε (g * k.val)) ∈ B := by
      rw [← Finset.mem_coe, hB]
      exact ⟨k, rfl⟩
    refine (Finset.le_sup (f := fun b => V.map (LinearMap.mulLeft ℂ b)) hk)
      (Submodule.mem_map.mpr ⟨fun g => φ (g * k.val), Submodule.subset_span ⟨k, rfl⟩, ?_⟩)
    funext g
    rfl
  · change cutoff r t S₀ ε (n.val * g) * φ (n.val * g) = cutoff r t S₀ ε g * φ g
    rw [cutoff_mul_left (unipotent_mem_parabolic n), hunip n g]
  · exact slice_cutoff_mul_mem (hslice k)

/-- Multiplying a section built from cusp forms spherical outside `S₁ ⊆ S₀` by the cutoff at
the places of `S₀` gives a section built from cusp forms spherical outside `S₀`. -/
theorem isSphericalSectionOutside_cutoff_mul {S₁ : Finset (FinitePlace F)} (hS : S₁ ⊆ S₀)
    {φ : AdelicGL F (r + t + 2) → ℂ} (hφ : IsSphericalSectionOutside T T' S₁ φ) :
    IsSphericalSectionOutside T T' S₀ (fun g => cutoff r t S₀ ε g * φ g) := by
  obtain ⟨hsph, hslice⟩ := hφ
  refine ⟨fun v hv k hk g => ?_, fun k => ?_⟩
  · change cutoff r t S₀ ε (g * adelicAt F (r + t + 2) v k) * φ (g * adelicAt F (r + t + 2) v k) =
      cutoff r t S₀ ε g * φ g
    rw [cutoff_mul_adelicAt hv, hsph v (fun h => hv (hS h)) k hk g]
  · have hmono := Submodule.span_mono (R := ℂ) (s := Set.range fun v :
          {x : T.Space // RankinSelbergGlobal.IsSphericalOutside F T S₁ x} ×
            {y : (dualRealization T').Space //
              RankinSelbergGlobal.IsSphericalOutside F (dualRealization T') S₁ y} =>
        fun m : FullLevi F (blockShape r t) =>
          ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v.1.1)
            (m (0 : Fin 2)) *
          ContinuousRationalFunctions.evaluate F (t + 1)
            ((dualRealization T').realization.toContinuous v.2.1) (m (1 : Fin 2)))
      (t := Set.range fun v :
          {x : T.Space // RankinSelbergGlobal.IsSphericalOutside F T S₀ x} ×
            {y : (dualRealization T').Space //
              RankinSelbergGlobal.IsSphericalOutside F (dualRealization T') S₀ y} =>
        fun m : FullLevi F (blockShape r t) =>
          ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v.1.1)
            (m (0 : Fin 2)) *
          ContinuousRationalFunctions.evaluate F (t + 1)
            ((dualRealization T').realization.toContinuous v.2.1) (m (1 : Fin 2))) (by
        rintro _ ⟨⟨x, y⟩, rfl⟩
        exact ⟨⟨⟨x.1, fun v hv => x.2 v (fun h => hv (hS h))⟩,
          ⟨y.1, fun v hv => y.2 v (fun h => hv (hS h))⟩⟩, rfl⟩)
    exact slice_cutoff_mul_mem (hmono (hslice k))

end Section

section Integrand

variable {S₀ : Finset (FinitePlace F)} {ε : ∀ v : FinitePlace F, FiniteCompletion F v}

/-- The global Whittaker coefficient is linear in constant factors. -/
theorem generalLinearWhittakerFunction_const_mul (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (m : Fin n → F) (c : ℂ)
    (f : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (n + 1)) (CommRingCat.of F)) → ℂ)
    (g : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (n + 1)) (CommRingCat.of F))) :
    generalLinearWhittakerFunction F n ψ m (fun x => c * f x) g =
      c * generalLinearWhittakerFunction F n ψ m f g := by
  unfold generalLinearWhittakerFunction subgroupCharacterCoefficient
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_const_mul c _

/-- The Levi Whittaker coefficient of `β f` at `h` is `β(h)` times that of `f`, since `β` is
left invariant under the Levi. -/
theorem leviWhittaker_cutoff_mul (ψ : AddChar (Adeles F) ℂ) (f : AdelicGL F (r + t + 2) → ℂ)
    (h : AdelicGL F (r + t + 2)) :
    leviWhittaker F r t ψ (fun g => cutoff r t S₀ ε g * f g) h =
      cutoff r t S₀ ε h * leviWhittaker F r t ψ f h := by
  unfold leviWhittaker
  have e : ∀ x y, cutoff r t S₀ ε (leviPair F r t x y * h) = cutoff r t S₀ ε h :=
    fun x y => cutoff_mul_left (leviEmbedding_mem_parabolic _) h
  simp_rw [e]
  simp_rw [generalLinearWhittakerFunction_const_mul]

/-- The open-cell integrand of `β φ` at `Y` is `β(w u'(Y))` times that of `φ`. -/
theorem openCellIntegrand_cutoff_mul (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ)
    (s : ℂ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    openCellIntegrand ψ (fun g => cutoff r t S₀ ε g * φ g) s Y =
      cutoff r t S₀ ε (openCellWeyl F r t * openCellUnipotent F r t Y) *
        openCellIntegrand ψ φ s Y := by
  unfold openCellIntegrand
  have e : (fun g => cutoff r t S₀ ε g * φ g * heightPower F r t s g) =
      fun g => cutoff r t S₀ ε g * (φ g * heightPower F r t s g) := by
    funext g
    ring
  rw [e, leviWhittaker_cutoff_mul, mul_assoc]

end Integrand

end Langlands.Global.CuspidalPairEisenstein.SemilocalCutoff
