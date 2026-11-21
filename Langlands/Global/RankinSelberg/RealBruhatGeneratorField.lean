import Langlands.Global.RankinSelberg.RealBruhatNormalAction

/-! # Smooth stabilizer directions along a real Bruhat cell -/

noncomputable section

open Filter Set Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.GeneralLinear.RealBruhatProductChart
open Langlands.GeneralLinear.RealBruhatTrailingChart
open scoped ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBruhatGeneratorField

open RealBruhatRootStabilizer RealBruhatNormalAction RealWhittakerGauge

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => upperUnipotent (r + 1) ℝ
local notation "P" => permutation (r + 1) ℝ

/-- The upper triangular factor of a zero-section point. -/
def upperFactor (w : Equiv.Perm (Fin (r + 1))) (x : Tangent w) : M :=
  upperProjection (r + 1) (combine w (x, 0))

/-- The right upper unipotent factor of a zero-section point. -/
def rightFactor (w : Equiv.Perm (Fin (r + 1))) (x : Tangent w) : M :=
  (P w)⁻¹.val * lowerFactorOfCoordinates (combine w (x, 0)) * (P w).val

private theorem isUpperTriangular_upperFactor (w : Equiv.Perm (Fin (r + 1))) (x : Tangent w) :
    (upperFactor w x).IsUpperTriangular := by
  intro i j hij
  simp [upperFactor, show j < i from hij]

private theorem isUnit_upperFactor (w : Equiv.Perm (Fin (r + 1))) {x : Tangent w}
    (hx : x ∈ tangentDomain w) : IsUnit (upperFactor w x) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular (isUpperTriangular_upperFactor w x),
    isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by simpa [upperFactor] using hx i

private theorem normal_entry_zero (w : Equiv.Perm (Fin (r + 1))) (x : Tangent w)
    {i j : Fin (r + 1)} (h : IsNormalEntry w (i, j)) : combine w (x, 0) i j = 0 := by
  change (if h' : IsNormalEntry w (i, j) then (0 : Normal w) ⟨(i, j), h'⟩
    else x ⟨(i, j), h'⟩) = 0
  simp only [dite_eq_left h, Pi.zero_apply]

/-- The explicit factors describe a zero-section matrix as an upper triangular
matrix times the permutation times an upper unipotent matrix. -/
theorem exists_factors (w : Equiv.Perm (Fin (r + 1))) (x : Tangent w)
    (hx : x ∈ tangentDomain w) :
    ∃ b : B, ∃ v : U, b.val.val = upperFactor w x ∧ v.val.val = rightFactor w x ∧
      productChart w (x, 0) = (b.val * P w * v.val).val := by
  let Y := combine w (x, 0)
  let L := lowerFactorOfCoordinates Y
  have hL₁ (i j : Fin (r + 1)) (hij : i < j) : L i j = 0 := by
    simp [L, lowerFactorOfCoordinates, Matrix.one_apply_ne hij.ne, not_lt_of_ge hij.le]
  have hL₂ (i : Fin (r + 1)) : L i i = 1 := by
    simp [L, lowerFactorOfCoordinates]
  have hL : IsUnit L := by
    have ht : L.transpose.IsUpperTriangular := fun i j hij => hL₁ j i hij
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose, Matrix.det_of_isUpperTriangular ht]
    simp [hL₂]
  let l : G := hL.unit
  have hl : l.val = L := IsUnit.unit_spec _
  let v₀ : G := (P w)⁻¹ * l * P w
  have hv₀ : v₀.val = rightFactor w x := by
    simp only [v₀, Units.val_mul, hl, L, Y, rightFactor]
  have he (i j : Fin (r + 1)) : v₀.val i j = L (w i) (w j) := by
    have h := permutation_conjugate_entry (r + 1) ℝ w⁻¹ l i j
    simpa only [← permutation_inv, inv_inv, hl] using h
  let v : U := ⟨v₀, by
    apply (mem_upperUnipotent_iff _ _ v₀).2
    refine ⟨fun i j hij => ?_, fun i => (he i i).trans (hL₂ (w i))⟩
    rw [he]
    rcases lt_or_gt_of_ne (fun h => hij.ne (w.injective h).symm) with h | h
    · exact hL₁ _ _ h
    · have hn : IsNormalEntry w (w i, w j) := ⟨h, by simpa using hij⟩
      simp [L, lowerFactorOfCoordinates, Matrix.one_apply_ne h.ne', h, Y, normal_entry_zero w x hn]⟩
  let b₀ : G := (isUnit_upperFactor w hx).unit
  have hb₀ : b₀.val = upperFactor w x := IsUnit.unit_spec _
  let b : B := ⟨b₀, by
    change b₀.val.IsUpperTriangular
    rw [hb₀]
    exact isUpperTriangular_upperFactor w x⟩
  refine ⟨b, v, hb₀, hv₀, ?_⟩
  have hprod : b.val * P w * v.val = b₀ * l * P w := by
    change b₀ * P w * ((P w)⁻¹ * l * P w) = _
    group
  rw [hprod, Units.val_mul, Units.val_mul, hb₀, hl]
  rfl

private theorem isUnit_rightFactor (w : Equiv.Perm (Fin (r + 1))) {x : Tangent w}
    (hx : x ∈ tangentDomain w) : IsUnit (rightFactor w x) := by
  obtain ⟨_, v, _, hv, _⟩ := exists_factors w x hx
  exact hv ▸ v.val.isUnit

private theorem contDiff_upperFactor (w : Equiv.Perm (Fin (r + 1))) :
    ContDiff ℝ ∞ (upperFactor w) :=
  (upperProjection (r + 1)).contDiff.comp ((combine w).toContinuousLinearMap.contDiff.comp
    (ContinuousLinearMap.inl ℝ (Tangent w) (Normal w)).contDiff)

private theorem contDiff_rightFactor (w : Equiv.Perm (Fin (r + 1))) :
    ContDiff ℝ ∞ (rightFactor w) := by
  have hY : ContDiff ℝ ∞ (fun x : Tangent w => combine w (x, 0)) :=
    (combine w).toContinuousLinearMap.contDiff.comp
      (ContinuousLinearMap.inl ℝ (Tangent w) (Normal w)).contDiff
  exact (contDiff_const.mul
    (contDiff_const.add (hY.sub (contDiff_upperFactor w)))).mul contDiff_const

private theorem contDiffOn_ringInverse_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {f : E → M} (hf : ContDiffOn ℝ ∞ f s)
    (hu : ∀ x ∈ s, IsUnit (f x)) : ContDiffOn ℝ ∞ (fun x => Ring.inverse (f x)) s := by
  intro x hx
  obtain ⟨u, h⟩ := hu x hx
  have hi : ContDiffAt ℝ ∞ Ring.inverse (f x) := h ▸ contDiffAt_ringInverse ℝ u
  exact hi.comp_contDiffWithinAt x (hf x hx)

/-- The left stabilizer generator as a matrix-valued function of the cell coordinate. -/
def leftField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (x : Tangent w) : M :=
  let q := upperFactor w x * (P w).val
  Neg.neg (q * rootMatrix i * Ring.inverse q)

/-- The right stabilizer generator as a matrix-valued function of the cell coordinate. -/
def rightField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (x : Tangent w) : M :=
  let v := rightFactor w x
  Ring.inverse v * rootMatrix i * v

theorem contDiffOn_leftField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) :
    ContDiffOn ℝ ∞ (leftField w i) (tangentDomain w) := by
  have hq : ContDiffOn ℝ ∞ (fun x => upperFactor w x * (P w).val) (tangentDomain w) :=
    ((contDiff_upperFactor w).mul contDiff_const).contDiffOn
  have hroot : ContDiffOn ℝ ∞ (fun _ : Tangent w => rootMatrix i) (tangentDomain w) :=
    contDiffOn_const
  exact ((hq.mul hroot).mul
    (contDiffOn_ringInverse_comp hq fun _ hx => (isUnit_upperFactor w hx).mul (P w).isUnit)).neg

theorem contDiffOn_rightField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) :
    ContDiffOn ℝ ∞ (rightField w i) (tangentDomain w) := by
  have hv := (contDiff_rightFactor w).contDiffOn (s := tangentDomain w)
  have hroot : ContDiffOn ℝ ∞ (fun _ : Tangent w => rootMatrix i) (tangentDomain w) :=
    contDiffOn_const
  exact ((contDiffOn_ringInverse_comp hv fun _ => isUnit_rightFactor w).mul hroot).mul hv

theorem leftField_eq (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (x : Tangent w)
    (b : B) (hb : b.val.val = upperFactor w x) : leftField w i x = leftGenerator b w i := by
  dsimp only [leftField, leftGenerator, conjRoot]
  rw [← hb, ← Units.val_mul, Ring.inverse_unit, inv_inv]

theorem rightField_eq (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (x : Tangent w)
    (v : U) (hv : v.val.val = rightFactor w x) : rightField w i x = rightGenerator v i := by
  dsimp only [rightField, rightGenerator, conjRoot]
  rw [← hv, Ring.inverse_unit]

/-- The varying paired stabilizer direction in the tangent and normal coordinates. -/
def pairedField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (z : Tangent w × Normal w) :
    Tangent w × Normal w :=
  let e := productChart w
  fderiv ℝ e.symm (e z) (leftField w i z.1 * e z + e z * rightField w i z.1)

theorem contDiffOn_pairedField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) :
    ContDiffOn ℝ ∞ (pairedField w i) (productChart w).source := by
  let e := productChart w
  have he := contDiffOn_productChart w
  have hi := ((contDiffOn_productChart_symm w).fderiv_of_isOpen e.open_target (by simp)).comp
    he (fun _ hz => e.map_source hz)
  have hfst : MapsTo Prod.fst e.source (tangentDomain w) := fun _ hz => hz.1
  have hl := (contDiffOn_leftField w i).comp contDiff_fst.contDiffOn hfst
  have hr := (contDiffOn_rightField w i).comp contDiff_fst.contDiffOn hfst
  exact hi.clm_apply ((hl.mul he).add (he.mul hr))

private theorem ambientGenerator_zero (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (b : B) (v : U) : ambientGenerator b v w i (b.val * P w * v.val).val = 0 := by
  let g := b.val * P w * v.val
  have hd := hasDerivAt_pairedAction b v w i g.val
  have hc : (fun t : ℝ => (leftUnit b w i t).val * g.val * (rightUnit v i t).val.val) =
      fun _ => g.val :=
    funext fun t => congrArg Units.val (leftUnit_mul_cell_mul_rightUnit b v w i t)
  rw [hc] at hd
  exact hd.unique (hasDerivAt_const 0 g.val)

theorem pairedField_zero (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (x : Tangent w)
    (hx : x ∈ tangentDomain w) : pairedField w i (x, 0) = 0 := by
  obtain ⟨b, v, hb, hv, hg⟩ := exists_factors w x hx
  change fderiv ℝ (productChart w).symm (productChart w (x, 0))
    (leftField w i x * _ + _ * rightField w i x) = 0
  rw [leftField_eq w i x b hb, rightField_eq w i x v hv, hg]
  change fderiv ℝ (productChart w).symm (b.val * P w * v.val).val
    (ambientGenerator b v w i (b.val * P w * v.val).val) = 0
  rw [ambientGenerator_zero, map_zero]

theorem fderiv_pairedField_normal (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (x : Tangent w) (hx : x ∈ tangentDomain w) (b : B) (v : U)
    (hb : b.val.val = upperFactor w x) (hv : v.val.val = rightFactor w x)
    (hg : productChart w (x, 0) = (b.val * P w * v.val).val) (y : Normal w) :
    fderiv ℝ (pairedField w i) (x, 0) (0, y) = chartGenerator b v w i x (0, y) := by
  let e := productChart w
  let I := ContinuousLinearMap.inr ℝ (Tangent w) (Normal w)
  let s : Normal w → Tangent w × Normal w := fun z => (x, 0) + I z
  let A := ambientGenerator b v w i
  let J' : (Tangent w × Normal w) → M →L[ℝ] (Tangent w × Normal w) :=
    fun z => fderiv ℝ e.symm (e z)
  have hx' : (x, 0) ∈ e.source := ⟨hx, mem_univ _⟩
  have hs : HasFDerivAt s I 0 := I.hasFDerivAt.const_add (x, 0)
  have hs₀ : s 0 = (x, 0) := by simp [s]
  have hsS : s 0 ∈ e.source := hs₀.symm ▸ hx'
  have he := ((contDiffOn_productChart w).contDiffAt (e.open_source.mem_nhds hsS)).differentiableAt
    (by simp)
  have hJ' : ContDiffOn ℝ ∞ J' e.source :=
    ((contDiffOn_productChart_symm w).fderiv_of_isOpen e.open_target (by simp)).comp
      (contDiffOn_productChart w) (fun _ hz => e.map_source hz)
  have hde := he.hasFDerivAt.comp 0 hs
  have hdA := A.hasFDerivAt.comp 0 hde
  have hdJ' := ((hJ'.contDiffAt (e.open_source.mem_nhds hsS)).differentiableAt
    (by simp)).hasFDerivAt.comp 0 hs
  have hzero : ambientGenerator b v w i (productChart w (x, 0)) = 0 := by
    rw [hg]
    exact ambientGenerator_zero w i b v
  have hD := (hdJ'.clm_apply hdA)
  have heq : (fun z => J' (s z) (A (e (s z)))) = pairedField w i ∘ s := by
    funext z
    have hz : (s z).1 = x := by simp [s, I]
    simp only [Function.comp_apply, pairedField, hz, leftField_eq w i x b hb,
      rightField_eq w i x v hv]
    rfl
  simp only [Function.comp_apply] at hD
  rw [heq] at hD
  have hdf := (((contDiffOn_pairedField w i).contDiffAt (e.open_source.mem_nhds hsS)).differentiableAt
    (by simp)).hasFDerivAt.comp 0 hs
  have hh := hdf.unique hD
  have hp := DFunLike.congr_fun hh y
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    add_apply, ContinuousLinearMap.flip_apply, hzero, map_zero, add_zero,
    hs₀, J', A, e, I, chartGenerator] using hp

theorem fderiv_pairedField_tangent (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (x : Tangent w) (hx : x ∈ tangentDomain w) (y : Tangent w) :
    fderiv ℝ (pairedField w i) (x, 0) (y, 0) = 0 := by
  let I := ContinuousLinearMap.inl ℝ (Tangent w) (Normal w)
  have hx' : I x ∈ (productChart w).source := ⟨hx, mem_univ _⟩
  have hD := (((contDiffOn_pairedField w i).contDiffAt
    ((productChart w).open_source.mem_nhds hx')).differentiableAt
    (by simp)).hasFDerivAt.comp x I.hasFDerivAt
  have hzero : pairedField w i ∘ I =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_tangentDomain w).mem_nhds hx] with z hz
    exact pairedField_zero w i z hz
  have hD₀ := (hasFDerivAt_const (𝕜 := ℝ) (0 : Tangent w × Normal w) x).congr_of_eventuallyEq hzero
  exact DFunLike.congr_fun (hD.unique hD₀) y

private theorem isNilpotent_of_tangent_zero {E N : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup N] [Module ℝ N] (f : Module.End ℝ (E × N)) (q : Module.End ℝ N)
    (ht : ∀ x : E, f (x, 0) = 0) (hn : ∀ z, (f z).2 = q z.2) (hq : IsNilpotent q) :
    IsNilpotent f := by
  have hpow (k : ℕ) (z : E × N) : ((f ^ k) z).2 = (q ^ k) z.2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hn, ih]
  obtain ⟨k, hk⟩ := hq
  refine ⟨k + 1, LinearMap.ext fun z => ?_⟩
  have hz : ((f ^ k) z).2 = 0 := by simp only [hpow, hk, LinearMap.zero_apply]
  have htan : (f ^ k) z = (((f ^ k) z).1, 0) := Prod.ext rfl hz
  rw [pow_succ', Module.End.mul_apply, htan, ht, LinearMap.zero_apply]

/-- The derivative of the varying paired field at the zero section is nilpotent. -/
theorem fderiv_pairedField_isNilpotent (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w) :
    IsNilpotent (fderiv ℝ (pairedField w i) (x, 0)).toLinearMap := by
  obtain ⟨b, v, hb, hv, hg⟩ := exists_factors w x hx
  let f := fderiv ℝ (pairedField w i) (x, 0)
  apply isNilpotent_of_tangent_zero f.toLinearMap (normalGenerator b v w i x).toLinearMap
    (fderiv_pairedField_tangent w i x hx) _ (normalGenerator_isNilpotent b v w i hi x hx hg)
  intro z
  have hz : z = (z.1, 0) + (0, z.2) := by ext <;> simp
  have he : f z = f (z.1, 0) + f (0, z.2) := by
    conv_lhs => rw [hz]
    exact map_add f _ _
  change (f z).2 = (chartGenerator b v w i x (0, z.2)).2
  rw [he, show f (z.1, 0) = 0 from fderiv_pairedField_tangent w i x hx z.1, zero_add]
  exact congrArg Prod.snd (fderiv_pairedField_normal w i x hx b v hb hv hg z.2)

theorem trace_fderiv_pairedField_eq_zero (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w) :
    LinearMap.trace ℝ (Tangent w × Normal w) (fderiv ℝ (pairedField w i) (x, 0)).toLinearMap = 0 :=
  (LinearMap.isNilpotent_trace_of_isNilpotent (fderiv_pairedField_isNilpotent w i hi x hx)).eq_zero

/-- The paired root field is smooth in the full chart, vanishes along the
cell, and has nilpotent derivative at every point of the cell. -/
def RealBruhatGeneratorFieldStatement : Prop :=
  ∀ (r : ℕ) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r), w i.castSucc < w i.succ →
    ContDiffOn ℝ ∞ (leftField w i) (tangentDomain w) ∧
    ContDiffOn ℝ ∞ (rightField w i) (tangentDomain w) ∧
    ContDiffOn ℝ ∞ (pairedField w i) (productChart w).source ∧
    ∀ x ∈ tangentDomain w, pairedField w i (x, 0) = 0 ∧
      IsNilpotent (fderiv ℝ (pairedField w i) (x, 0)).toLinearMap

theorem realBruhatGeneratorField : RealBruhatGeneratorFieldStatement := by
  intro r w i hi
  exact ⟨contDiffOn_leftField w i, contDiffOn_rightField w i, contDiffOn_pairedField w i,
    fun x hx => ⟨pairedField_zero w i x hx, fderiv_pairedField_isNilpotent w i hi x hx⟩⟩

end Langlands.Global.RankinSelbergGlobal.RealBruhatGeneratorField
