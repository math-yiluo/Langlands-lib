import Langlands.Representation.RestrictedTensor.Scalars

/-! # Normalized bilinear forms on actual restricted tensor products -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uV
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.RestrictedTensor.Pairing

variable {K : Type uK} [Field K] {ι : Type uI} {V : ι → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (C : ∀ i, V i →ₗ[K] V i →ₗ[K] K)

/-- Tensor the local forms at one finite stage and multiply the scalar factors. -/
def stage (S : Finset ι) : Stage K V S →ₗ[K] Stage K V S →ₗ[K] K :=
  (PiTensorProduct.piTensorHomMap₂ (PiTensorProduct.tprod K (fun i : S => C i))).compr₂
    (scalarStageEquiv K S).toLinearMap

@[simp]
theorem stage_tprod (S : Finset ι) (v w : ∀ i : S, V i) :
    stage C S (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w) =
      ∏ i : S, C i (v i) (w i) := by
  simp only [stage, LinearMap.compr₂_apply, PiTensorProduct.piTensorHomMap₂_tprod_tprod_tprod,
    LinearEquiv.coe_coe, scalarStageEquiv_tprod]

variable (E : Finset ι) (e : ∀ i, V i) (hnorm : ∀ i ∉ E, C i (e i) (e i) = 1)

include hnorm in
/-- The normalized finite forms agree after adjoining reference vectors. -/
theorem stage_transition {S T : Finset ι} (hES : E ⊆ S) (h : S ⊆ T)
    (x y : Stage K V S) :
    stage C T (transition e h x) (transition e h y) = stage C S x y := by
  suffices heq : (stage C T).compl₁₂ (transition e h) (transition e h) = stage C S from
    LinearMap.congr_fun (LinearMap.congr_fun heq x) y
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro w
  change stage C T (transition e h (PiTensorProduct.tprod K v))
      (transition e h (PiTensorProduct.tprod K w)) =
    stage C S (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w)
  rw [transition_tprod, transition_tprod, stage_tprod, stage_tprod]
  let f : ι → K := fun i =>
    if hi : i ∈ S then C i (v ⟨i, hi⟩) (w ⟨i, hi⟩) else 1
  have hext (i : T) : C i (extend e v i) (extend e w i) = f i := by
    by_cases hi : i.1 ∈ S
    · simp [f, extend, hi]
    · simp [f, extend, hi, hnorm i (fun hiE => hi (hES hiE))]
  calc
    (∏ i : T, C i (extend e v i) (extend e w i)) = ∏ i : T, f i :=
      Finset.prod_congr rfl fun i _ => hext i
    _ = ∏ i ∈ T, f i := Finset.prod_coe_sort T f
    _ = ∏ i ∈ S, f i :=
      (Finset.prod_subset h fun i _ hi => by simp [f, hi]).symm
    _ = ∏ i : S, f i := (Finset.prod_coe_sort S f).symm
    _ = ∏ i : S, C i (v i) (w i) :=
      Finset.prod_congr rfl fun i _ => by simp [f, i.2]

private def value : Space K V E e → Space K V E e → K :=
  DirectLimit.lift₂ (systemMap K V E e) (systemMap K V E e)
    (fun S x y => stage C S.1 x y)
    (fun S _T h x y => (stage_transition C E e hnorm S.2 h x y).symm)

private theorem value_of (S : Index E) (x y : Stage K V S.1) :
    value C E e hnorm (of K V E e S x) (of K V E e S y) = stage C S.1 x y := by
  unfold value of
  apply DirectLimit.lift₂_def

/-- The actual bilinear form on the algebraic restricted tensor product. -/
def form : Space K V E e →ₗ[K] Space K V E e →ₗ[K] K :=
  LinearMap.mk₂ K (value C E e hnorm)
    (fun x y z => DirectLimit.induction₃ (systemMap K V E e) (fun S a b c => by
      simp only [value, DirectLimit.add_def, DirectLimit.lift₂_def, map_add,
        LinearMap.add_apply]) x y z)
    (fun c x y => DirectLimit.induction₂ (systemMap K V E e) (fun S a b => by
      simp only [value, DirectLimit.smul_def, DirectLimit.lift₂_def, map_smul,
        LinearMap.smul_apply]) x y)
    (fun x y z => DirectLimit.induction₃ (systemMap K V E e) (fun S a b c => by
      simp only [value, DirectLimit.add_def, DirectLimit.lift₂_def, map_add]) x y z)
    (fun c x y => DirectLimit.induction₂ (systemMap K V E e) (fun S a b => by
      simp only [value, DirectLimit.smul_def, DirectLimit.lift₂_def, map_smul]) x y)

@[simp]
theorem form_of (S : Index E) (x y : Stage K V S.1) :
    form C E e hnorm (of K V E e S x) (of K V E e S y) = stage C S.1 x y :=
  value_of C E e hnorm S x y

@[simp]
theorem form_pure (S : Index E) (v w : ∀ i : S.1, V i) :
    form C E e hnorm (pure E e S v) (pure E e S w) = ∏ i : S.1, C i (v i) (w i) := by
  rw [pure, pure, form_of, stage_tprod]

private theorem exists_bilinear_ne_zero {W : Type*} [AddCommGroup W] [Module K W]
    (B : W →ₗ[K] W →ₗ[K] K) (hB : B ≠ 0) : ∃ x y, B x y ≠ 0 := by
  by_contra h
  apply hB
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact not_not.mp fun hxy => h ⟨x, y, hxy⟩

/-- Nonzero local forms give a nonzero restricted tensor form. -/
theorem form_ne_zero (hC : ∀ i, C i ≠ 0) : form C E e hnorm ≠ 0 := by
  choose a b hab using fun i : E => exists_bilinear_ne_zero (C i) (hC i)
  intro hzero
  have hv := congrArg (fun B : Space K V E e →ₗ[K] Space K V E e →ₗ[K] K =>
    B (pure E e ⟨E, le_rfl⟩ a) (pure E e ⟨E, le_rfl⟩ b)) hzero
  have hp : (∏ i : E, C i (a i) (b i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hab i
  exact hp (by simpa only [form_pure, LinearMap.zero_apply] using hv)

theorem stage_invariant (S : Finset ι) (P Q : ∀ i, Module.End K (V i))
    (hC : ∀ i x y, C i (P i x) (Q i y) = C i x y)
    (x y : Stage K V S) :
    stage C S (PiTensorProduct.map (fun i : S => P i) x)
      (PiTensorProduct.map (fun i : S => Q i) y) = stage C S x y := by
  suffices heq : (stage C S).compl₁₂
      (PiTensorProduct.map (fun i : S => P i))
      (PiTensorProduct.map (fun i : S => Q i)) = stage C S from
    LinearMap.congr_fun (LinearMap.congr_fun heq x) y
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro w
  change stage C S (PiTensorProduct.map _ (PiTensorProduct.tprod K v))
      (PiTensorProduct.map _ (PiTensorProduct.tprod K w)) =
    stage C S (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w)
  simp only [PiTensorProduct.map_tprod, stage_tprod, hC]

private theorem map_of_of_subset (P : ∀ i, Module.End K (V i))
    (hP : ∀ᶠ i in Filter.cofinite, P i (e i) = e i)
    (S : Index E) (hS : mapBound E hP ⊆ S.1) (x : Stage K V S.1) :
    map E E e e P hP (of K V E e S x) =
      of K V E e S (PiTensorProduct.map (fun i : S.1 => P i) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simpa only [pure, map_smul, PiTensorProduct.map_tprod] using
      congrArg (a • ·) (map_pure_of_subset E E e e P hP S hS v)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Invariance of all component forms gives invariance of the actual restricted
tensor form under the two induced componentwise maps. -/
theorem form_map_invariant (P Q : ∀ i, Module.End K (V i))
    (hP : ∀ᶠ i in Filter.cofinite, P i (e i) = e i)
    (hQ : ∀ᶠ i in Filter.cofinite, Q i (e i) = e i)
    (hC : ∀ i x y, C i (P i x) (Q i y) = C i x y)
    (x y : Space K V E e) :
    form C E e hnorm (map E E e e P hP x) (map E E e e Q hQ y) =
      form C E e hnorm x y := by
  obtain ⟨S, a, b, rfl, rfl⟩ :=
    DirectLimit.exists_eq_mk₂ (systemMap K V E e) x y
  let T : Index E :=
    ⟨S.1 ∪ (mapBound E hP ∪ mapBound E hQ), S.2.trans Finset.subset_union_left⟩
  have hST : S ≤ T := Finset.subset_union_left
  change form C E e hnorm (map E E e e P hP (of K V E e S a))
      (map E E e e Q hQ (of K V E e S b)) =
    form C E e hnorm (of K V E e S a) (of K V E e S b)
  rw [← of_transition E e hST a, ← of_transition E e hST b]
  rw [map_of_of_subset E e P hP T (Finset.subset_union_left.trans Finset.subset_union_right),
    map_of_of_subset E e Q hQ T (Finset.subset_union_right.trans Finset.subset_union_right),
    form_of, form_of]
  exact stage_invariant C T.1 P Q hC _ _

end Langlands.RestrictedTensor.Pairing
