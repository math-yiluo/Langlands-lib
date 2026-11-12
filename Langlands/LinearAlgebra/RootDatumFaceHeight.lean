import Langlands.LinearAlgebra.RootDatumBasedCorrection
import Langlands.LinearAlgebra.RootDatumCoweightFace
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # The face height of a based root datum

For a base `B` of a root datum and a coweight `ν`, the face height is the
`ℤ`-linear form on the root span that sends a simple root to `0` when it
vanishes on `ν` and to `1` otherwise. When `ν` is dominant for `B`, the face
height vanishes on the roots vanishing on `ν`, is at least `1` on the roots
positive on `ν`, and is invariant under every automorphism fixing `ν` that
admits a based correction.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function

namespace Langlands.LinearAlgebra.RootDatumFaceHeight

open RootDatumWeylChambers RootDatumBasedCorrection

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum J M N}

/-- A root-datum automorphism maps the root span into itself. -/
theorem smul_mem_rootSpan (g : P.Aut) {x : M} (hx : x ∈ P.rootSpan ℤ) :
    g • x ∈ P.rootSpan ℤ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← RootPairing.Equiv.root_indexEquiv_eq_smul]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [smul_add]
    exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

/-- The restriction of a root-datum automorphism to the root span. -/
def rootSpanMap (g : P.Aut) : P.rootSpan ℤ →ₗ[ℤ] P.rootSpan ℤ where
  toFun x := ⟨g • (x : M), smul_mem_rootSpan g x.2⟩
  map_add' x y := by
    ext
    simp [smul_add]
  map_smul' a x := by
    ext
    simp [smul_comm g a (x : M)]

@[simp]
theorem coe_rootSpanMap (g : P.Aut) (x : P.rootSpan ℤ) :
    (rootSpanMap g x : M) = g • (x : M) :=
  rfl

theorem rootSpanMap_one : rootSpanMap (1 : P.Aut) = LinearMap.id := by
  ext x
  simp

theorem rootSpanMap_mul (g g' : P.Aut) :
    rootSpanMap (g * g') = (rootSpanMap g).comp (rootSpanMap g') := by
  ext x
  change (g * g') • (x : M) = g • g' • (x : M)
  exact mul_smul g g' (x : M)

theorem rootSpanMap_rootSpanMem (g : P.Aut) (i : J) :
    rootSpanMap g (P.rootSpanMem ℤ i) = P.rootSpanMem ℤ (g.indexEquiv i) := by
  ext
  simp

variable (B : P.Base) (ν : N)

/-- The face height: the linear form on the root span sending a simple root to
`0` if it vanishes on `ν` and to `1` otherwise. -/
def faceHeight : P.rootSpan ℤ →ₗ[ℤ] ℤ :=
  B.toWeightBasisInt.constr ℤ fun i => if P.root' i ν = 0 then 0 else 1

theorem faceHeight_simple (i : J) (hi : i ∈ B.support) :
    faceHeight B ν (P.rootSpanMem ℤ i) = if P.root' i ν = 0 then 0 else 1 := by
  have h : P.rootSpanMem ℤ i = B.toWeightBasisInt ⟨i, hi⟩ := by
    ext
    simp
  rw [h, faceHeight, Module.Basis.constr_basis]

/-- The face height of a combination of simple roots. -/
theorem faceHeight_eq_sum (x : P.rootSpan ℤ) (f : J → ℤ)
    (hx : (x : M) = ∑ j ∈ B.support, f j • P.root j) :
    faceHeight B ν x = ∑ j ∈ B.support, f j * if P.root' j ν = 0 then 0 else 1 := by
  have hx' : x = ∑ j ∈ B.support, f j • P.rootSpanMem ℤ j := by
    ext
    simp [hx]
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_zsmul, faceHeight_simple B ν j hj, smul_eq_mul]

/-- The value of `ν` on a combination of simple roots. -/
theorem root'_eq_sum {j : J} (f : J → ℤ)
    (hx : P.root j = ∑ i ∈ B.support, f i • P.root i) :
    P.root' j ν = ∑ i ∈ B.support, f i * P.root' i ν := by
  change P.toLinearMap (P.root j) ν = _
  rw [hx]
  simp [map_sum, LinearMap.sum_apply]

variable {B ν}

private theorem sum_mul_indicator_eq_zero (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (f : J → ℤ) (hf : ∀ i ∈ B.support, 0 ≤ f i)
    (hsum : ∑ i ∈ B.support, f i * P.root' i ν = 0) :
    ∑ i ∈ B.support, f i * (if P.root' i ν = 0 then 0 else 1) = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => mul_nonneg (hf i hi) (hdom i hi))).mp hsum
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases h : P.root' i ν = 0
  · simp [h]
  · have := hterm i hi
    rcases mul_eq_zero.mp this with h' | h'
    · simp [h']
    · exact absurd h' h

/-- When `ν` is dominant, the face height vanishes on the roots vanishing on `ν`. -/
theorem faceHeight_root_of_eq_zero (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (j : J) (hj : P.root' j ν = 0) :
    faceHeight B ν (P.rootSpanMem ℤ j) = 0 := by
  obtain ⟨f, -, hf | hf⟩ := B.exists_root_eq_sum_nat_or_neg j
  · have hz : P.root j = ∑ i ∈ B.support, (f i : ℤ) • P.root i := by
      simp [hf]
    rw [faceHeight_eq_sum B ν _ _ hz]
    apply sum_mul_indicator_eq_zero hdom _ (fun i _ => Int.natCast_nonneg _)
    rw [← root'_eq_sum B ν _ hz, hj]
  · have hz : P.root j = ∑ i ∈ B.support, (-(f i : ℤ)) • P.root i := by
      simp [hf, neg_smul, Finset.sum_neg_distrib]
    rw [faceHeight_eq_sum B ν _ _ hz]
    have h := sum_mul_indicator_eq_zero hdom (fun i => (f i : ℤ))
      (fun i _ => Int.natCast_nonneg _) (by
        have h' := root'_eq_sum B ν _ hz
        rw [hj] at h'
        simp only [neg_mul, Finset.sum_neg_distrib] at h'
        linarith)
    simp only [neg_mul, Finset.sum_neg_distrib, h, neg_zero]

/-- When `ν` is dominant, the face height is at least `1` on the roots positive
on `ν`. -/
theorem one_le_faceHeight_root_of_pos (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (j : J) (hj : 0 < P.root' j ν) :
    1 ≤ faceHeight B ν (P.rootSpanMem ℤ j) := by
  obtain ⟨f, -, hf | hf⟩ := B.exists_root_eq_sum_nat_or_neg j
  · have hz : P.root j = ∑ i ∈ B.support, (f i : ℤ) • P.root i := by
      simp [hf]
    rw [faceHeight_eq_sum B ν _ _ hz]
    rw [root'_eq_sum B ν _ hz] at hj
    obtain ⟨i, hi, hpos⟩ := Finset.exists_lt_of_sum_lt (by simpa using hj :
      ∑ i ∈ B.support, (0 : ℤ) < ∑ i ∈ B.support, (f i : ℤ) * P.root' i ν)
    have hne : P.root' i ν ≠ 0 := by
      rintro h
      simp [h] at hpos
    have hfi : 1 ≤ (f i : ℤ) := by
      rcases Nat.eq_zero_or_pos (f i) with h | h
      · simp [h] at hpos
      · exact_mod_cast h
    calc (1 : ℤ) ≤ (f i : ℤ) * if P.root' i ν = 0 then 0 else 1 := by simpa [hne] using hfi
      _ ≤ ∑ i ∈ B.support, (f i : ℤ) * if P.root' i ν = 0 then 0 else 1 :=
        Finset.single_le_sum (f := fun i => (f i : ℤ) * if P.root' i ν = 0 then 0 else 1)
          (fun i _ => mul_nonneg (Int.natCast_nonneg _) (by split_ifs <;> norm_num)) hi
  · exfalso
    have hz : P.root j = ∑ i ∈ B.support, (-(f i : ℤ)) • P.root i := by
      simp [hf, neg_smul, Finset.sum_neg_distrib]
    rw [root'_eq_sum B ν _ hz] at hj
    have : ∑ i ∈ B.support, (-(f i : ℤ)) * P.root' i ν ≤ 0 :=
      Finset.sum_nonpos fun i hi =>
        mul_nonpos_of_nonpos_of_nonneg (by simp) (hdom i hi)
    omega

/-- When `ν` is dominant, reflections at roots vanishing on `ν` preserve the face
height. -/
theorem faceHeight_comp_rootSpanMap_of_mem (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    {w : P.Aut} (hw : w ∈ reflectionSubgroup P {i | P.root' i ν = 0}) :
    (faceHeight B ν).comp (rootSpanMap w) = faceHeight B ν := by
  induction hw using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    ext x
    have hx : rootSpanMap (RootPairing.Equiv.reflection P j) x =
        x - (P.toLinearMap (x : M) (P.coroot j)) • P.rootSpanMem ℤ j := by
      ext
      simp [RootPairing.reflection_apply]
    simp only [LinearMap.comp_apply, hx, map_sub, map_zsmul,
      faceHeight_root_of_eq_zero hdom j hj, smul_zero, sub_zero]
  | one => rw [rootSpanMap_one, LinearMap.comp_id]
  | mul a b _ _ ha hb => rw [rootSpanMap_mul, ← LinearMap.comp_assoc, ha, hb]
  | inv a _ ha =>
    calc (faceHeight B ν).comp (rootSpanMap a⁻¹)
        = ((faceHeight B ν).comp (rootSpanMap a)).comp (rootSpanMap a⁻¹) := by rw [ha]
      _ = faceHeight B ν := by
        rw [LinearMap.comp_assoc, ← rootSpanMap_mul, mul_inv_cancel, rootSpanMap_one,
          LinearMap.comp_id]

/-- When `ν` is dominant, every automorphism admitting a based correction for
`ν` and `B` preserves the face height. -/
theorem faceHeight_comp_rootSpanMap (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    {δ : P.Aut} (C : Correction P ν B δ) :
    (faceHeight B ν).comp (rootSpanMap δ) = faceHeight B ν := by
  have hw := faceHeight_comp_rootSpanMap_of_mem hdom C.weyl.property
  have hwinv := faceHeight_comp_rootSpanMap_of_mem hdom (inv_mem C.weyl.property)
  have hθ : (faceHeight B ν).comp (rootSpanMap (C.weyl.val * δ)) = faceHeight B ν := by
    apply B.toWeightBasisInt.ext
    intro i
    have hb : B.toWeightBasisInt i = P.rootSpanMem ℤ i := by
      ext
      simp
    rw [LinearMap.comp_apply, hb, rootSpanMap_rootSpanMem, ← C.index_eq i,
      faceHeight_simple B ν _ (C.perm i).2, faceHeight_simple B ν _ i.2]
    have hz := C.zero_iff i
    by_cases h : P.root' i ν = 0
    · simp [h, hz.mp h]
    · have h' : P.root' (C.perm i) ν ≠ 0 := fun h' => h (hz.mpr h')
      simp [h, h']
  calc (faceHeight B ν).comp (rootSpanMap δ)
      = (faceHeight B ν).comp (rootSpanMap (C.weyl.val⁻¹ * (C.weyl.val * δ))) := by
        rw [inv_mul_cancel_left]
    _ = ((faceHeight B ν).comp (rootSpanMap C.weyl.val⁻¹)).comp
          (rootSpanMap (C.weyl.val * δ)) := by
        rw [rootSpanMap_mul, LinearMap.comp_assoc]
    _ = faceHeight B ν := by rw [hwinv, hθ]

/-- For a base on which `ν` is dominant, the coroots of the roots vanishing on `ν`
span the same lattice as the simple ones among them. -/
theorem coroot_span_zero_eq_of_dominant [Fintype J] (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν) :
    Submodule.span ℤ (P.coroot '' {i | P.root' i ν = 0}) =
      Submodule.span ℤ (P.coroot '' {i | i ∈ B.support ∧ P.root' i ν = 0}) := by
  let q := P.flip.toLinearMap ν
  let g : Module.Dual ℤ N := q ∘ₗ P.CoPolarization
  have hz (i : J) : g (P.coroot i) = 0 ↔ P.root' i ν = 0 :=
    dual_copolarization_coroot_eq_zero_iff P q i
  have hpos (i : J) : 0 < g (P.coroot i) ↔ 0 < P.root' i ν :=
    GroupScheme.SplitExistence.dual_polarization_root_pos_iff P.flip q i
  have hnonneg (i : J) (hi : i ∈ B.support) : 0 ≤ g (P.coroot i) := by
    rcases (hdom i hi).eq_or_lt with h | h
    · exact ((hz i).mpr h.symm).ge
    · exact ((hpos i).mpr h).le
  have h := coroot_span_zero_eq_span_simple P B g hnonneg
  simpa only [hz] using h

/-- For a base on which `ν` is dominant, a weight annihilates the coroots of all
roots vanishing on `ν` if and only if it annihilates the simple ones among them. -/
theorem annihilator_iff_of_dominant [Fintype J] (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (x : M) :
    (∀ i, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0) ↔
      ∀ i ∈ B.support, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0 := by
  constructor
  · exact fun h i _ hi => h i hi
  · intro h i hi
    have hspan : Submodule.span ℤ
        (P.coroot '' {i | i ∈ B.support ∧ P.root' i ν = 0}) ≤
        LinearMap.ker (P.toLinearMap x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      exact h j hj.1 hj.2
    apply hspan
    rw [← coroot_span_zero_eq_of_dominant hdom]
    exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- **Range transfer through an injective pullback.** Let `g` be injective with
image the annihilator of the coroots of the roots vanishing on `μ`, and let the
image of `g ∘ π` be the annihilator of the coroots of the roots vanishing on `ν`,
where `ν` is dominant for `B`. Then `x` lies in the image of `π` exactly when
`g x` annihilates the simple coroots of the simple roots vanishing on `ν` but
not on `μ`. -/
theorem mem_range_iff_of_dominant [Fintype J] {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν) (μ : N)
    (g : V →ₗ[ℤ] M) (hg : Function.Injective g)
    (hgr : ∀ χ, χ ∈ LinearMap.range g ↔
      ∀ i, P.root' i μ = 0 → P.toLinearMap χ (P.coroot i) = 0)
    (π : W →ₗ[ℤ] V)
    (hgπ : ∀ χ, χ ∈ LinearMap.range (g ∘ₗ π) ↔
      ∀ i, P.root' i ν = 0 → P.toLinearMap χ (P.coroot i) = 0)
    (x : V) :
    x ∈ LinearMap.range π ↔
      ∀ i ∈ B.support, P.root' i μ ≠ 0 → P.root' i ν = 0 →
        P.toLinearMap (g x) (P.coroot i) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i _ _ hz
    exact (hgπ (g (π y))).mp ⟨y, rfl⟩ i hz
  · intro h
    have hx : g x ∈ LinearMap.range (g ∘ₗ π) := by
      rw [hgπ, annihilator_iff_of_dominant hdom]
      intro i hi hz
      by_cases hμ : P.root' i μ = 0
      · exact (hgr (g x)).mp ⟨x, rfl⟩ i hμ
      · exact h i hi hμ hz
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hg hy⟩

/-- The base of a coweight face is dominant for its coweight. -/
theorem face_dominant [Fintype J] [P.IsReduced] {ν : N} (C : RootDatumCoweightFace.Face P ν) :
    ∀ i ∈ C.base.support, 0 ≤ P.root' i ν := by
  intro i hi
  by_cases h : P.root' i ν = 0
  · exact h.ge
  · have hmem : i ∈ IsAddIndecomposable.baseOf P.root
        ((P.flip.toLinearMap C.regular) : M →+ ℤ) := by
      rw [← C.support_eq]
      exact hi
    exact ((C.signs i h).mp hmem.1).le

end Langlands.LinearAlgebra.RootDatumFaceHeight
