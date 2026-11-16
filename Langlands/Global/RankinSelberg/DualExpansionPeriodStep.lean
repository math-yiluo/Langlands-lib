import Langlands.Global.RankinSelberg.DualExpansionInduction

/-! # The period step of the dual expansion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic ratVec ratVec_apply)

variable {F : Type u} [Field F] [NumberField F]

local instance dualPerSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualPerSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {m K : ℕ}

section Basic

theorem continuous_rowPoint : Continuous (rowPoint F (m := m) (K := K)) := by
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K + 1)).symm.continuous.comp ?_
  have h : Continuous fun b : Fin m → Adeles F => rowMat m K b := by
    refine continuous_pi fun a => continuous_pi fun j => ?_
    simp only [rowMat]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  exact Units.continuous_iff.mpr ⟨continuous_const.add h, continuous_const.sub h⟩

theorem continuous_superSum : Continuous (superSum F (K := K)) := by
  unfold superSum
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact (continuous_apply _).comp ((continuous_apply _).comp continuous_pointMatrix)
  · exact continuous_const

theorem continuous_joinRect :
    Continuous fun p : (Fin K × Fin m → Adeles F) × (Fin m → Adeles F) => joinRect p.1 p.2 := by
  refine continuous_pi fun k => ?_
  simp only [joinRect]
  cases rectSplit.symm k with
  | inl j => exact (continuous_apply j).comp continuous_snd
  | inr q => exact (continuous_apply q).comp continuous_fst

theorem joinRect_add {R : Type*} [Add R] (x₁ x₂ : Fin K × Fin m → R) (b₁ b₂ : Fin m → R) :
    joinRect (x₁ + x₂) (b₁ + b₂) = joinRect x₁ b₁ + joinRect x₂ b₂ := by
  funext k
  simp only [joinRect, Pi.add_apply]
  cases rectSplit.symm k <;> rfl

theorem joinRect_ratVec (ρ : Fin K × Fin m → F) (σ : Fin m → F) :
    joinRect (ratVec ρ) (ratVec σ) = ratVec (K := F) (joinRect ρ σ) := by
  funext k
  rw [ratVec_apply]
  simp only [joinRect]
  cases rectSplit.symm k <;> rfl

theorem joinRect_add_ratVec (x' : Fin K × Fin m → Adeles F) (b : Fin m → Adeles F)
    (ρ : Fin K × Fin m → F) :
    joinRect (x' + ratVec ρ) b = joinRect x' b + ratVec (K := F) (joinRect ρ (0 : Fin m → F)) := by
  funext k
  rw [Pi.add_apply, ratVec_apply]
  simp only [joinRect]
  cases rectSplit.symm k with
  | inl j => simp
  | inr q => simp [ratVec]

/-- `ψ` of the superdiagonal sum is trivial on rational unipotent points. -/
theorem superSum_rational_char {ψ : AddChar (Adeles F) ℂ}
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) {g : unipotentAdelic F K}
    (hg : g ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K)) :
    ψ (superSum F (g : Points F K)) = 1 := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff g).mp hg
  have : superSum F (g : Points F K) = algebraMap F (Adeles F)
      (∑ i : Fin K, if h : (i : ℕ) + 1 < K then (M : Matrix (Fin K) (Fin K) F) i ⟨(i : ℕ) + 1, h⟩
        else 0) := by
    unfold superSum
    rw [hM, pointMatrix_symm_rational, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [this, hψF]

end Basic

variable [CompactSpace (AdeleQuotient F)]

section Defs

variable (ψ : AddChar (Adeles F) ℂ)

/-- The row integral `J(u, c', b')` of the column step. -/
def rowJ (V : Points F (m + K + 1) → ℂ) (u : unipotentAdelic F K) (c' : Fin K → Adeles F)
    (b' : Fin m → Adeles F) : ℂ :=
  Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) fun x' =>
    cornerSum F m K V (xcPoint F x' c' * midPoint F (u : Points F K) * rowPoint F b')

/-- The rectangle integral of the column step with the last row `b` fixed. -/
def colPsi (W : Points F (m + (K + 1) + 1) → ℂ) (y : Points F (m + (K + 1) + 1))
    (u : unipotentAdelic F K) (c' : Fin K → Adeles F) (b : Fin m → Adeles F) : ℂ :=
  Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) fun x' =>
    rectInner ψ (cornerSum F m (K + 1) W)
      (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
        (xcPoint F 0 c' * midPoint F (u : Points F K)) * y) (joinRect x' b)

end Defs

section RowJ

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {V : Points F (m + K + 1) → ℂ}
include hψF

theorem DualData.continuous_rowJ (hV : DualData F m ψ K V) :
    Continuous fun p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F) =>
      rowJ V p.1 p.2.1 p.2.2 := by
  unfold rowJ
  refine Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral
    (F := fun (p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F))
      (x' : Fin K × Fin m → Adeles F) =>
        cornerSum F m K V (xcPoint F x' p.2.1 * midPoint F (p.1 : Points F K) * rowPoint F p.2.2))
    ?_ (fun p => ?_)
  · have h1 : Continuous fun q : (unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F)) ×
        (Fin K × Fin m → Adeles F) => xcPoint F q.2 q.1.2.1 :=
      (continuous_xcPoint (F := F) (m := m) (K := K)).comp
        (f := fun q : (unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F)) ×
          (Fin K × Fin m → Adeles F) => (q.2, q.1.2.1)) (by fun_prop)
    have h2 : Continuous fun q : (unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F)) ×
        (Fin K × Fin m → Adeles F) => midPoint F (m := m) (q.1.1 : Points F K) :=
      continuous_midPoint.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    have h3 : Continuous fun q : (unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F)) ×
        (Fin K × Fin m → Adeles F) => rowPoint F (m := m) (K := K) q.1.2.2 :=
      continuous_rowPoint.comp ((continuous_snd.comp continuous_snd).comp continuous_fst)
    exact (hV.continuous_cornerSum.comp ((h1.mul h2).mul h3)).congr fun q => rfl
  · have := hV.isPeriodic_rect hψF p.2.1 (midPoint F (p.1 : Points F K) * rowPoint F p.2.2)
    simpa only [mul_assoc] using this

theorem DualData.isPeriodic_rowJ (hV : DualData F m ψ K V) (u : unipotentAdelic F K)
    (b' : Fin m → Adeles F) : IsPeriodic fun c' => rowJ V u c' b' := by
  intro c' σ
  refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun x' => ?_
  have h := hV.isPeriodic_col hψF x' (midPoint F (u : Points F K) * rowPoint F b') c' σ
  simpa only [mul_assoc] using h

end RowJ

section RowJPeriod

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  (hψc : Continuous ψ) {V : Points F (m + K + 1) → ℂ}

include hψF hψc in
/-- The dual period at a row point, written through the row integrals. -/
theorem DualData.dualPeriod_eq_rowJ (hV : DualData F m ψ K V) (b' : Fin m → Adeles F) :
    dualPeriod F m K ψ V (rowPoint F b') = unipotentPeriod F K fun u =>
      ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) fun c' =>
          ψ (lastEntry c') * rowJ V u c' b' := by
  unfold dualPeriod
  refine congrArg (unipotentPeriod F K) (funext fun u => ?_)
  refine congrArg (ψ (superSum F (u : Points F K)) * ·) ?_
  have hcont : Continuous (Function.uncurry fun (c' : Fin K → Adeles F)
      (x' : Fin K × Fin m → Adeles F) => ψ (lastEntry c') *
        cornerSum F m K V (xcPoint F x' c' * midPoint F (u : Points F K) * rowPoint F b')) := by
    have h1 : Continuous fun p : (Fin K → Adeles F) × (Fin K × Fin m → Adeles F) =>
        xcPoint F p.2 p.1 :=
      (continuous_xcPoint (F := F) (m := m) (K := K)).comp
        (f := fun p : (Fin K → Adeles F) × (Fin K × Fin m → Adeles F) => (p.2, p.1))
        (by fun_prop)
    exact ((hψc.comp (continuous_lastEntry.comp continuous_fst)).mul
      (hV.continuous_cornerSum.comp ((h1.mul continuous_const).mul continuous_const))).congr
        fun _ => rfl
  have hper : ∀ (c' : Fin K → Adeles F) (x' : Fin K × Fin m → Adeles F) (σ : Fin K → F)
      (ρ : Fin K × Fin m → F),
      ψ (lastEntry (c' + ratVec σ)) * cornerSum F m K V (xcPoint F (x' + ratVec ρ) (c' + ratVec σ) *
        midPoint F (u : Points F K) * rowPoint F b') =
      ψ (lastEntry c') * cornerSum F m K V (xcPoint F x' c' * midPoint F (u : Points F K) *
        rowPoint F b') := by
    intro c' x' σ ρ
    have h1 : ψ (lastEntry (c' + ratVec σ)) = ψ (lastEntry c') := isPeriodic_lastEntry hψF c' σ
    have h2 : cornerSum F m K V (xcPoint F (x' + ratVec ρ) (c' + ratVec σ) *
        midPoint F (u : Points F K) * rowPoint F b') = cornerSum F m K V
          (xcPoint F x' (c' + ratVec σ) * midPoint F (u : Points F K) * rowPoint F b') := by
      have := hV.isPeriodic_rect hψF (c' + ratVec σ)
        (midPoint F (u : Points F K) * rowPoint F b') x' ρ
      simpa only [mul_assoc] using this
    have h3 : cornerSum F m K V (xcPoint F x' (c' + ratVec σ) * midPoint F (u : Points F K) *
        rowPoint F b') = cornerSum F m K V
          (xcPoint F x' c' * midPoint F (u : Points F K) * rowPoint F b') := by
      have := hV.isPeriodic_col hψF x' (midPoint F (u : Points F K) * rowPoint F b') c' σ
      simpa only [mul_assoc] using this
    rw [h1, h2, h3]
  have hcomm := Langlands.Automorphic.CuspidalWhittaker.torusIntegral_comm hcont hper
  unfold rowJ rectPeriod
  refine Eq.trans ?_ (hcomm.symm.trans
    (Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun c' =>
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral_const_mul _ _))
  simp only [mul_assoc]

end RowJPeriod

section ColPsi

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
  (hψn : ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1)
  {W : Points F (m + (K + 1) + 1) → ℂ}

include hψF hψc in
theorem DualData.continuous_colPsi (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) :
    Continuous fun p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F) =>
      colPsi ψ W y p.1 p.2.1 p.2.2 := by
  unfold colPsi
  have hφ : Continuous fun p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F) =>
      pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
        (xcPoint F 0 p.2.1 * midPoint F (p.1 : Points F K)) * y := by
    have hxc : Continuous fun p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F) =>
        xcPoint F (m := m) (0 : Fin K × Fin m → Adeles F) p.2.1 :=
      (continuous_xcPoint_right 0).comp (continuous_fst.comp continuous_snd)
    have hmid : Continuous fun p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F) =>
        midPoint F (m := m) (p.1 : Points F K) :=
      continuous_midPoint.comp (continuous_subtype_val.comp continuous_fst)
    have hpad := (continuous_pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)).comp
      (hxc.mul hmid)
    exact hpad.mul continuous_const
  have h := hW.continuous_rectInner_param hψF hψc hφ
  have hj : Continuous fun q : (unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F)) ×
      (Fin K × Fin m → Adeles F) => (q.1, joinRect q.2 q.1.2.2) :=
    continuous_fst.prodMk (continuous_joinRect.comp (continuous_snd.prodMk
      ((continuous_snd.comp continuous_snd).comp continuous_fst)))
  refine Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral
    (F := fun (p : unipotentAdelic F K × (Fin K → Adeles F) × (Fin m → Adeles F))
      (x' : Fin K × Fin m → Adeles F) => rectInner ψ (cornerSum F m (K + 1) W)
        (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
          (xcPoint F 0 p.2.1 * midPoint F (p.1 : Points F K)) * y) (joinRect x' p.2.2))
    ((h.comp hj).congr fun q => rfl) (fun p => ?_)
  intro x' ρ
  show rectInner ψ (cornerSum F m (K + 1) W) _ (joinRect (x' + ratVec ρ) p.2.2) =
    rectInner ψ (cornerSum F m (K + 1) W) _ (joinRect x' p.2.2)
  rw [joinRect_add_ratVec]
  exact hW.isPeriodic_rectInner hψF _ _ _

include hψF hψc hψ1 hψn in
/-- The column-step rectangle integral as a sum of row integrals (P2). -/
theorem DualData.colPsi_eq_tsum (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    (u : unipotentAdelic F K) (c' : Fin K → Adeles F) (b : Fin m → Adeles F) :
    colPsi ψ W y u c' b = ∑' β : Fin m → F,
      rowJ (dualPullback W y) u c' (b + fun j => algebraMap F (Adeles F) (β j)) :=
  hW.torusIntegral_rect_col hψF hψc hψ1 hψn y c' u b

include hψF hψc hψ1 hψn in
theorem DualData.isPeriodic_colPsi_col (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) (u : unipotentAdelic F K) (b : Fin m → Adeles F) :
    IsPeriodic fun c' => colPsi ψ W y u c' b := by
  intro c' σ
  show colPsi ψ W y u (c' + ratVec σ) b = colPsi ψ W y u c' b
  rw [hW.colPsi_eq_tsum hψF hψc hψ1 hψn, hW.colPsi_eq_tsum hψF hψc hψ1 hψn]
  exact tsum_congr fun β => (hW.pullbackData hψF y).isPeriodic_rowJ hψF u _ c' σ

include hψF hψc hψ1 hψn in
theorem DualData.isPeriodic_colPsi_row (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) (u : unipotentAdelic F K) (c' : Fin K → Adeles F) :
    IsPeriodic fun b => colPsi ψ W y u c' b := by
  intro b ρ
  show colPsi ψ W y u c' (b + ratVec ρ) = colPsi ψ W y u c' b
  rw [hW.colPsi_eq_tsum hψF hψc hψ1 hψn, hW.colPsi_eq_tsum hψF hψc hψ1 hψn]
  have hb : ∀ β : Fin m → F, (b + ratVec ρ + fun j => algebraMap F (Adeles F) (β j)) =
      b + fun j => algebraMap F (Adeles F) ((Equiv.addLeft ρ β) j) := by
    intro β
    funext j
    simp only [Pi.add_apply, ratVec_apply, Equiv.coe_addLeft, map_add, add_assoc]
  exact (tsum_congr fun β => congrArg (rowJ (dualPullback W y) u c') (hb β)).trans
    ((Equiv.addLeft ρ).tsum_eq fun β' =>
      rowJ (dualPullback W y) u c' (b + fun j => algebraMap F (Adeles F) (β' j)))

include hψF in
theorem DualData.exists_rowJ_bound (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) :
    ∃ C : ℝ, ∀ (u : unipotentAdelic F K) (c' : Fin K → Adeles F) (b : Fin m → Adeles F),
      Summable (fun β : Fin m → F =>
        ‖rowJ (dualPullback W y) u c' (b + fun j => algebraMap F (Adeles F) (β j))‖) ∧
      ∑' β : Fin m → F,
        ‖rowJ (dualPullback W y) u c' (b + fun j => algebraMap F (Adeles F) (β j))‖ ≤ C := by
  obtain ⟨C, hC⟩ := hW.rowJ_bound hψF y
  exact ⟨C, fun u c' b => hC c' u b⟩

include hψF hψc hψ1 hψn in
theorem DualData.norm_colPsi_le (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    {C : ℝ} (hC : ∀ (u : unipotentAdelic F K) (c' : Fin K → Adeles F) (b : Fin m → Adeles F),
      Summable (fun β : Fin m → F =>
        ‖rowJ (dualPullback W y) u c' (b + fun j => algebraMap F (Adeles F) (β j))‖) ∧
      ∑' β : Fin m → F,
        ‖rowJ (dualPullback W y) u c' (b + fun j => algebraMap F (Adeles F) (β j))‖ ≤ C)
    (u : unipotentAdelic F K) (c' : Fin K → Adeles F) (b : Fin m → Adeles F) :
    ‖colPsi ψ W y u c' b‖ ≤ C := by
  rw [hW.colPsi_eq_tsum hψF hψc hψ1 hψn]
  exact (norm_tsum_le_tsum_norm (hC u c' b).1).trans (hC u c' b).2

include hψF hψc in
/-- **First reduction of the period step** (S1): the last-column decomposition of the unipotent
period, with the rectangle period split along its last row. -/
theorem DualData.dualPeriod_succ_col (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) :
    dualPeriod F m (K + 1) ψ W y = unipotentPeriod F K (fun u =>
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
        ψ (lastEntry c' + superSum F (u : Points F K)) *
          Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m)
            (fun b => colPsi ψ W y u c' b))) := by
  have hcont : Continuous fun u₁ : unipotentAdelic F (K + 1) =>
      ψ (superSum F (u₁ : Points F (K + 1))) *
        rectPeriod F m (K + 1) ψ (cornerSum F m (K + 1) W)
          (midPoint F (u₁ : Points F (K + 1)) * y) :=
    (hψc.comp (continuous_superSum.comp continuous_subtype_val)).mul
      (hW.continuous_rectPeriod_param hψF hψc
        ((continuous_midPoint.comp continuous_subtype_val).mul continuous_const))
  have hinv : ∀ g ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (K + 1))
      (upperUnipotent F (K + 1)), ∀ h : unipotentAdelic F (K + 1),
      ψ (superSum F ((g * h : unipotentAdelic F (K + 1)) : Points F (K + 1))) *
        rectPeriod F m (K + 1) ψ (cornerSum F m (K + 1) W)
          (midPoint F ((g * h : unipotentAdelic F (K + 1)) : Points F (K + 1)) * y) =
      ψ (superSum F (h : Points F (K + 1))) *
        rectPeriod F m (K + 1) ψ (cornerSum F m (K + 1) W)
          (midPoint F (h : Points F (K + 1)) * y) := by
    intro g hg h
    rw [Subgroup.coe_mul, superSum_mul F _ _ (isUnitriangular_of_mem_unipotentAdelic F g)
      (isUnitriangular_of_mem_unipotentAdelic F h), AddChar.map_add_eq_mul,
      superSum_rational_char hψF hg, one_mul, hW.rectPeriod_midPoint_rat_mul hψF hψc hg]
  unfold dualPeriod
  rw [unipotentPeriod_succ _ hcont hinv]
  refine congrArg (unipotentPeriod F K) (funext fun u => ?_)
  refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun c' => ?_
  rw [midPoint_colHom_padHom, Subgroup.coe_mul, coe_colHom, coe_padHom,
    superSum_lastColPoint_mul_pad, toAdd_ofAdd, rectPeriod_eq_rectInner,
    torusIntegral_rect_succ (hW.isPeriodic_rectInner hψF _) (hW.continuous_rectInner hψF hψc _)]
  rfl

include hψF hψc hψ1 hψn in
/-- Exchanging the column and last-row torus integrals in the period step. -/
theorem DualData.colStep_swap (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    (u : unipotentAdelic F K) :
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
        ψ (lastEntry c' + superSum F (u : Points F K)) *
          Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m)
            (fun b => colPsi ψ W y u c' b)) =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m) (fun b =>
        ψ (superSum F (u : Points F K)) *
          Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
            (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b)) := by
  have h1 : ∀ c' : Fin K → Adeles F, ψ (lastEntry c' + superSum F (u : Points F K)) *
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m)
        (fun b => colPsi ψ W y u c' b) =
      ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m)
          (fun b => ψ (lastEntry c') * colPsi ψ W y u c' b) := by
    intro c'
    rw [AddChar.map_add_eq_mul, Langlands.Automorphic.CuspidalWhittaker.torusIntegral_const_mul]
    ring
  rw [Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr h1,
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral_const_mul,
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral_const_mul (ψ (superSum F (u : Points F K)))
      (fun b => Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
        (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b))]
  refine congrArg (ψ (superSum F (u : Points F K)) * ·) ?_
  have hΨ := hW.continuous_colPsi hψF hψc y
  have hcont : Continuous (Function.uncurry fun (c' : Fin K → Adeles F) (b : Fin m → Adeles F) =>
      ψ (lastEntry c') * colPsi ψ W y u c' b) := by
    have hu : Continuous fun p : (Fin K → Adeles F) × (Fin m → Adeles F) => (u, p.1, p.2) :=
      continuous_const.prodMk (continuous_fst.prodMk continuous_snd)
    exact ((hψc.comp (continuous_lastEntry.comp continuous_fst)).mul (hΨ.comp hu)).congr
      fun _ => rfl
  refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_comm hcont ?_
  intro c' b σ ρ
  have e1 : ψ (lastEntry (c' + ratVec σ)) = ψ (lastEntry c') := isPeriodic_lastEntry hψF c' σ
  have e2 : colPsi ψ W y u (c' + ratVec σ) (b + ratVec ρ) = colPsi ψ W y u c' (b + ratVec ρ) :=
    hW.isPeriodic_colPsi_col hψF hψc hψ1 hψn y u (b + ratVec ρ) c' σ
  have e3 : colPsi ψ W y u c' (b + ratVec ρ) = colPsi ψ W y u c' b :=
    hW.isPeriodic_colPsi_row hψF hψc hψ1 hψn y u c' b ρ
  show ψ (lastEntry (c' + ratVec σ)) * colPsi ψ W y u (c' + ratVec σ) (b + ratVec ρ) =
    ψ (lastEntry c') * colPsi ψ W y u c' b
  rw [e1, e2, e3]

include hψF hψc hψ1 hψn in
/-- The period step for a fixed last row `b`: the unipotent period of the column integral is the
sum over `β ∈ F^m` of the dual periods of the pullback at the row points `b + β`. -/
theorem DualData.periodStep_row (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) (b : Fin m → Adeles F) :
    unipotentPeriod F K (fun u => ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
          (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b)) =
      ∑' β : Fin m → F, dualPeriod F m K ψ (dualPullback W y)
        (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) := by
  have hV : DualData F m ψ K (dualPullback W y) := hW.pullbackData hψF y
  obtain ⟨C, hC⟩ := hW.exists_rowJ_bound hψF y
  have hJ := hV.continuous_rowJ hψF
  have hgc : ∀ (b' : Fin m → Adeles F) (u : unipotentAdelic F K),
      Continuous fun c' : Fin K → Adeles F => ψ (lastEntry c') * rowJ (dualPullback W y) u c' b' :=
    fun b' u => by
      have hq : Continuous fun c' : Fin K → Adeles F => (u, c', b') :=
        continuous_const.prodMk (continuous_id.prodMk continuous_const)
      exact ((hψc.comp continuous_lastEntry).mul (hJ.comp hq)).congr fun _ => rfl
  have hgp : ∀ (b' : Fin m → Adeles F) (u : unipotentAdelic F K),
      IsPeriodic fun c' : Fin K → Adeles F => ψ (lastEntry c') * rowJ (dualPullback W y) u c' b' :=
    fun b' u => (isPeriodic_lastEntry hψF).mul (hV.isPeriodic_rowJ hψF u b')
  have hgs : ∀ (u : unipotentAdelic F K) (c' : Fin K → Adeles F), Summable fun β : Fin m → F =>
      ‖ψ (lastEntry c') * rowJ (dualPullback W y) u c'
        (b + fun j => algebraMap F (Adeles F) (β j))‖ := by
    intro u c'
    simp only [norm_mul, hψ1, one_mul]
    exact (hC u c' b).1
  have hgB : ∀ (u : unipotentAdelic F K) (c' : Fin K → Adeles F), ∑' β : Fin m → F,
      ‖ψ (lastEntry c') * rowJ (dualPullback W y) u c'
        (b + fun j => algebraMap F (Adeles F) (β j))‖ ≤ C := by
    intro u c'
    simp only [norm_mul, hψ1, one_mul]
    exact (hC u c' b).2
  have hfin : ∀ (u : unipotentAdelic F K) (s : Finset (Fin m → F)), ∑ β ∈ s,
      ‖ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
          ψ (lastEntry c') * rowJ (dualPullback W y) u c'
            (b + fun j => algebraMap F (Adeles F) (β j)))‖ ≤ C := by
    intro u s
    simp only [norm_mul (ψ _), hψ1, one_mul]
    exact sum_norm_torusIntegral_le (fun β => hgc _ u) (fun β => hgp _ u) (hgs u) (hgB u) s
  have hfs : ∀ u : unipotentAdelic F K, Summable fun β : Fin m → F =>
      ‖ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
          ψ (lastEntry c') * rowJ (dualPullback W y) u c'
            (b + fun j => algebraMap F (Adeles F) (β j)))‖ :=
    fun u => summable_of_sum_le (fun _ => norm_nonneg _) (hfin u)
  have hfuc : ∀ β : Fin m → F, Continuous fun u : unipotentAdelic F K =>
      ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
          ψ (lastEntry c') * rowJ (dualPullback W y) u c'
            (b + fun j => algebraMap F (Adeles F) (β j))) := by
    intro β
    have hq : Continuous fun q : unipotentAdelic F K × (Fin K → Adeles F) =>
        (q.1, q.2, b + fun j => algebraMap F (Adeles F) (β j)) :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
    refine (hψc.comp (continuous_superSum.comp continuous_subtype_val)).mul ?_
    exact Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral
      (F := fun (u : unipotentAdelic F K) (c' : Fin K → Adeles F) =>
        ψ (lastEntry c') * rowJ (dualPullback W y) u c'
          (b + fun j => algebraMap F (Adeles F) (β j)))
      (((hψc.comp (continuous_lastEntry.comp continuous_snd)).mul (hJ.comp hq)).congr
        fun _ => rfl) (fun u => hgp _ u)
  have hrhs : ∀ β : Fin m → F, dualPeriod F m K ψ (dualPullback W y)
      (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) =
      unipotentPeriod F K (fun u => ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
          ψ (lastEntry c') * rowJ (dualPullback W y) u c'
            (b + fun j => algebraMap F (Adeles F) (β j)))) :=
    fun β => hV.dualPeriod_eq_rowJ hψF hψc _
  rw [tsum_congr hrhs, ← unipotentPeriod_tsum _ hfuc hfs
    (fun u => (hfs u).tsum_le_of_sum_le (hfin u))]
  refine congrArg (unipotentPeriod F K) (funext fun u => ?_)
  rw [tsum_mul_left]
  refine congrArg (ψ (superSum F (u : Points F K)) * ·) ?_
  rw [← torusIntegral_tsum (fun β => hgc _ u) (fun β => hgp _ u) (hgs u) (hgB u)]
  refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun c' => ?_
  rw [hW.colPsi_eq_tsum hψF hψc hψ1 hψn, tsum_mul_left]

include hψF hψc hψ1 hψn in
/-- **The period step of the dual expansion**: the dual period at rank `m + K + 2` is the
integral over the last row `b ∈ (F \ 𝔸)^m` of the sum over `β ∈ F^m` of the dual periods of the
pullback at rank `m + K + 1`, evaluated at the row points `b + β`. -/
theorem DualData.dualPeriod_succ (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) :
    dualPeriod F m (K + 1) ψ W y =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m) fun b =>
        ∑' β : Fin m → F, dualPeriod F m K ψ (dualPullback W y)
          (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) := by
  obtain ⟨C, hC⟩ := hW.exists_rowJ_bound hψF y
  have hΨb : ∀ u c' b, ‖colPsi ψ W y u c' b‖ ≤ C := hW.norm_colPsi_le hψF hψc hψ1 hψn y hC
  have hΨ := hW.continuous_colPsi hψF hψc y
  have hGc : Continuous fun p : unipotentAdelic F K × (Fin m → Adeles F) =>
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
        (fun c' => ψ (lastEntry c') * colPsi ψ W y p.1 c' p.2) := by
    have hq : Continuous fun q : (unipotentAdelic F K × (Fin m → Adeles F)) × (Fin K → Adeles F) =>
        (q.1.1, q.2, q.1.2) :=
      (continuous_fst.comp continuous_fst).prodMk (continuous_snd.prodMk
        (continuous_snd.comp continuous_fst))
    refine Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral
      (F := fun (p : unipotentAdelic F K × (Fin m → Adeles F)) (c' : Fin K → Adeles F) =>
        ψ (lastEntry c') * colPsi ψ W y p.1 c' p.2)
      (((hψc.comp (continuous_lastEntry.comp continuous_snd)).mul (hΨ.comp hq)).congr
        fun _ => rfl) (fun p => ?_)
    exact (isPeriodic_lastEntry hψF).mul (hW.isPeriodic_colPsi_col hψF hψc hψ1 hψn y p.1 p.2)
  have hfc : Continuous (Function.uncurry fun (u : unipotentAdelic F K) (b : Fin m → Adeles F) =>
      ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
          (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b)) :=
    ((hψc.comp (continuous_superSum.comp (continuous_subtype_val.comp continuous_fst))).mul
      hGc).congr fun _ => rfl
  have hfp : ∀ u : unipotentAdelic F K, IsPeriodic fun b : Fin m → Adeles F =>
      ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
          (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b) := by
    intro u b ρ
    have e : ∀ c', ψ (lastEntry c') * colPsi ψ W y u c' (b + ratVec ρ) =
        ψ (lastEntry c') * colPsi ψ W y u c' b := fun c' => by
      rw [show colPsi ψ W y u c' (b + ratVec ρ) = colPsi ψ W y u c' b from
        hW.isPeriodic_colPsi_row hψF hψc hψ1 hψn y u c' b ρ]
    show ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
          (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' (b + ratVec ρ)) = _
    rw [Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr e]
  have hfb : ∀ (u : unipotentAdelic F K) (b : Fin m → Adeles F),
      ‖ψ (superSum F (u : Points F K)) *
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
          (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b)‖ ≤ C := by
    intro u b
    rw [norm_mul, hψ1, one_mul]
    refine norm_torusIntegral_le fun c' => ?_
    rw [norm_mul, hψ1, one_mul]
    exact hΨb u c' b
  have hswap : ∀ u : unipotentAdelic F K,
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) (fun c' =>
        ψ (lastEntry c' + superSum F (u : Points F K)) *
          Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m)
            (fun b => colPsi ψ W y u c' b)) =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m) (fun b =>
        ψ (superSum F (u : Points F K)) *
          Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
            (fun c' => ψ (lastEntry c') * colPsi ψ W y u c' b)) :=
    fun u => hW.colStep_swap hψF hψc hψ1 hψn y u
  rw [hW.dualPeriod_succ_col hψF hψc y, congrArg (unipotentPeriod F K) (funext hswap),
    unipotentPeriod_torusIntegral_comm _ hfc hfp hfb]
  exact Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun b =>
    hW.periodStep_row hψF hψc hψ1 hψn y b

end ColPsi

end Langlands.Global.RankinSelbergGlobal.Unfolding
