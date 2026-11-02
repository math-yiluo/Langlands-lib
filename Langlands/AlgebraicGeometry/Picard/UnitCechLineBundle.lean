import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleGauge
import Langlands.Cohomology.CechRefine

/-! # Ordered actual-unit cocycles and glued line bundles -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard.UnitCechLineBundle

open Langlands.Cohomology Cech

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- The actual structure-sheaf units with additive notation. -/
abbrev unitP : TopCat.Presheaf AddCommGrpCat.{u} X :=
  NilpotentUnitReduction.unitsPresheaf X.presheaf

/-- The underlying function of an additively written actual unit. -/
def unitVal {W : X.Opens} (a : (unitP (X := X)).obj (op W)) : Γ(X, W) :=
  (a.toMul : (Γ(X, W))ˣ).val

lemma unitVal_injective (W : X.Opens) :
    Function.Injective (unitVal (X := X) (W := W)) := by
  intro a b h
  exact congrArg Additive.ofMul (Units.ext h : a.toMul = b.toMul)

/-- The pairwise units of an ordered actual-unit one-cochain. -/
def pairUnits (z : C (unitP (X := X)) U 1) (i j : ι) : (Γ(X, U i ⊓ U j))ˣ :=
  (res (Cech.inter_two (U := U) i j).ge (z ![i, j])).toMul

lemma res_pairUnits_val (z : C (unitP (X := X)) U 1) (i j : ι)
    {W : X.Opens} (hW : W ≤ U i ⊓ U j) :
    X.presheaf.map (homOfLE hW).op (pairUnits U z i j : Γ(X, U i ⊓ U j)) =
      unitVal (res (hW.trans (Cech.inter_two (U := U) i j).ge) (z ![i, j])) := by
  change unitVal (res hW (res (Cech.inter_two (U := U) i j).ge (z ![i, j]))) = _
  rw [res_res]

/-- Pairwise transition units determine an ordered one-cochain. -/
lemma pairUnits_injective : Function.Injective (pairUnits U) := by
  intro z w h
  funext σ
  have hσ : ![σ 0, σ 1] = σ := by
    funext i
    fin_cases i <;> rfl
  have e := congrFun (congrFun h (σ 0)) (σ 1)
  have e' := congrArg Additive.ofMul e
  change res _ (z ![σ 0, σ 1]) = res _ (w ![σ 0, σ 1]) at e'
  have e'' := congrArg (res (P := unitP (X := X))
    (le_inf (inter_le_apply σ 0) (inter_le_apply σ 1))) e'
  simp only [res_res] at e''
  rw [Cech.res_congr (unitP (X := X)) U hσ z _ le_rfl,
    Cech.res_congr (unitP (X := X)) U hσ w _ le_rfl] at e''
  simpa only [res_self] using e''

/-- Closed ordered unit cochains give multiplicative transition cocycles. -/
lemma isCocycle_pairUnits {z : C (unitP (X := X)) U 1}
    (hz : d (unitP (X := X)) U 1 z = 0) :
    CocycleGluing.IsCocycle (pairUnits U z) := by
  intro i j k
  rw [res_pairUnits_val, res_pairUnits_val, res_pairUnits_val]
  exact congrArg (unitVal (X := X))
    (cocycle_add hz i j k _ _ _)

/-- The actual line bundle glued from a closed ordered unit cochain on a full cover. -/
def lineBundle (hU : (⨆ i, U i) = ⊤) (z : C (unitP (X := X)) U 1)
    (hz : d (unitP (X := X)) U 1 z = 0) : LineBundle X :=
  ⟨CocycleGluing.glued (pairUnits U z),
    CocycleGluing.isLocallyFreeRankOne_glued _ hU (isCocycle_pairUnits U hz)⟩

/-- The vertex units of an ordered actual-unit zero-cochain. -/
def vertexUnits (a : C (unitP (X := X)) U 0) (i : ι) : (Γ(X, U i))ˣ :=
  (res (inter_const_one i).ge (a (fun _ => i))).toMul

lemma res_vertexUnits_val (a : C (unitP (X := X)) U 0) (i : ι)
    {W : X.Opens} (hW : W ≤ U i) :
    X.presheaf.map (homOfLE hW).op (vertexUnits U a i : Γ(X, U i)) =
      unitVal (res (hW.trans (inter_const_one i).ge) (a (fun _ => i))) := by
  change unitVal (res hW (res (inter_const_one i).ge (a (fun _ => i)))) = _
  rw [res_res]

lemma vertexUnits_neg (a : C (unitP (X := X)) U 0) (i : ι) :
    vertexUnits U (-a) i = (vertexUnits U a i)⁻¹ := by
  change (res (inter_const_one i).ge (-a (fun _ => i))).toMul = _
  rw [map_neg]
  rfl

/-- Write a family of vertex units as an ordered zero-cochain. -/
def vertexCochain (a : ∀ i : ι, (Γ(X, U i))ˣ) : C (unitP (X := X)) U 0 :=
  fun σ => res (inter_le_apply σ 0) (Additive.ofMul (a (σ 0)))

lemma vertexUnits_vertexCochain (a : ∀ i : ι, (Γ(X, U i))ˣ) :
    vertexUnits U (vertexCochain U a) = a := by
  funext i
  change (res (P := unitP (X := X)) (inter_const_one i).ge
    (res (inter_le_apply (fun _ : Fin 1 => i) 0) (Additive.ofMul (a i)))).toMul = a i
  rw [res_res, res_self]
  rfl

/-- A zero-cochain differential changes the glued transition cocycle by a unit gauge.
The inverse vertex units account for the convention d a(i,j) = a(j) - a(i). -/
lemma isGauge_of_d_eq_sub {z w : C (unitP (X := X)) U 1}
    {a : C (unitP (X := X)) U 0} (ha : d (unitP (X := X)) U 0 a = w - z) :
    CocycleGluing.IsGauge (pairUnits U z) (pairUnits U w)
      (fun i => (vertexUnits U a i)⁻¹) := by
  apply (CocycleGluing.isGauge_iff _ _ _).2
  intro i j
  have h := congrArg (res (Cech.inter_two (U := U) i j).ge) (congrFun ha ![i, j])
  change res _ (d (unitP (X := X)) U 0 a ![i, j]) =
    res _ (w ![i, j] - z ![i, j]) at h
  rw [res_d_zero_pair a i j _ (inf_le_left.trans (inter_const_one i).ge)
    (inf_le_right.trans (inter_const_one j).ge), map_sub] at h
  have h' :
      -res (inf_le_left.trans (inter_const_one i).ge) (a (fun _ => i)) +
        res (Cech.inter_two (U := U) i j).ge (z ![i, j]) =
      res (Cech.inter_two (U := U) i j).ge (w ![i, j]) +
        -res (inf_le_right.trans (inter_const_one j).ge) (a (fun _ => j)) := by
    calc
      _ = (res (inf_le_right.trans (inter_const_one j).ge) (a (fun _ => j)) -
          res (inf_le_left.trans (inter_const_one i).ge) (a (fun _ => i))) +
          res (Cech.inter_two (U := U) i j).ge (z ![i, j]) -
          res (inf_le_right.trans (inter_const_one j).ge) (a (fun _ => j)) := by abel
      _ = _ := by rw [h]; abel
  change _ * _ = _ * _
  dsimp only
  rw [← vertexUnits_neg U a i, ← vertexUnits_neg U a j,
    res_vertexUnits_val, res_vertexUnits_val]
  change unitVal (-res (inf_le_left.trans (inter_const_one i).ge) (a (fun _ => i)) +
      res (Cech.inter_two (U := U) i j).ge (z ![i, j])) =
    unitVal (res (Cech.inter_two (U := U) i j).ge (w ![i, j]) +
      -res (inf_le_right.trans (inter_const_one j).ge) (a (fun _ => j)))
  exact congrArg (unitVal (X := X)) h'

/-- The gauge equation recovers the zero-cochain differential, with the same sign convention. -/
lemma d_eq_sub_of_isGauge {z w : C (unitP (X := X)) U 1}
    {a : C (unitP (X := X)) U 0}
    (ha : CocycleGluing.IsGauge (pairUnits U z) (pairUnits U w)
      (fun i => (vertexUnits U a i)⁻¹)) :
    d (unitP (X := X)) U 0 a = w - z := by
  apply pairUnits_injective U
  funext i j
  apply Units.ext
  have h := (CocycleGluing.isGauge_iff _ _ _).1 ha i j
  dsimp only at h
  rw [← vertexUnits_neg U a i, ← vertexUnits_neg U a j,
    res_vertexUnits_val, res_vertexUnits_val] at h
  change unitVal (-res (inf_le_left.trans (inter_const_one i).ge) (a (fun _ => i)) +
      res (Cech.inter_two (U := U) i j).ge (z ![i, j])) =
    unitVal (res (Cech.inter_two (U := U) i j).ge (w ![i, j]) +
      -res (inf_le_right.trans (inter_const_one j).ge) (a (fun _ => j))) at h
  have h' := unitVal_injective _ h
  change unitVal (res (Cech.inter_two (U := U) i j).ge
      (d (unitP (X := X)) U 0 a ![i, j])) =
    unitVal (res (Cech.inter_two (U := U) i j).ge (w ![i, j] - z ![i, j]))
  apply congrArg (unitVal (X := X))
  rw [res_d_zero_pair a i j _ (inf_le_left.trans (inter_const_one i).ge)
    (inf_le_right.trans (inter_const_one j).ge), map_sub]
  rw [← sub_eq_zero] at h' ⊢
  convert h' using 1
  abel

/-- Transition gauges exist exactly when the ordered cochains differ by a coboundary. -/
lemma exists_isGauge_iff {z w : C (unitP (X := X)) U 1} :
    (∃ b : ∀ i : ι, (Γ(X, U i))ˣ,
      CocycleGluing.IsGauge (pairUnits U z) (pairUnits U w) b) ↔
    ∃ a : C (unitP (X := X)) U 0, d (unitP (X := X)) U 0 a = w - z := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨-(vertexCochain U b), d_eq_sub_of_isGauge U ?_⟩
    convert hb using 1
    funext i
    rw [vertexUnits_neg, vertexUnits_vertexCochain, inv_inv]
  · rintro ⟨a, ha⟩
    exact ⟨_, isGauge_of_d_eq_sub U ha⟩

/-- On any open family, the glued sheaves from closed ordered unit cochains are isomorphic
exactly when their difference is a zero-cochain differential. -/
lemma nonempty_iso_glued_iff {z w : C (unitP (X := X)) U 1}
    (hz : d (unitP (X := X)) U 1 z = 0) (hw : d (unitP (X := X)) U 1 w = 0) :
    Nonempty (CocycleGluing.glued (pairUnits U z) ≅
      CocycleGluing.glued (pairUnits U w)) ↔
    ∃ a : C (unitP (X := X)) U 0, d (unitP (X := X)) U 0 a = w - z := by
  rw [CocycleGluing.nonempty_iso_glued_iff
    (isCocycle_pairUnits U hz) (isCocycle_pairUnits U hw)]
  exact exists_isGauge_iff U

end Langlands.AlgebraicGeometry.Picard.UnitCechLineBundle
