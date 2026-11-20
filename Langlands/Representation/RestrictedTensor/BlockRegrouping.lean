import Langlands.Representation.RestrictedTensor.Maps
import Langlands.Representation.Tensor.FiniteRegrouping
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Regrouping a restricted tensor of block coefficient spaces

At a common finite stage, transpose the block and place indices. The finite
stage maps agree with adjoining the specified reference tensors.
-/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uR uI uJ uV uW

namespace Langlands.FiniteTensor

variable (R : Type uR) [CommRing R]
variable {I : Type uI} {J : Type uJ}
variable (V : I → J → Type uV)
variable [∀ i j, AddCommGroup (V i j)] [∀ i j, Module R (V i j)]

private abbrev sigmaSwap : (Σ _ : I, J) ≃ (Σ _ : J, I) where
  toFun p := ⟨p.2, p.1⟩
  invFun p := ⟨p.2, p.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transpose two finite tensor indices by regrouping the same family of factors. -/
def transposeLinearEquiv [Finite I] [Finite J] :
    (⨂[R] i, (⨂[R] j, V i j)) ≃ₗ[R] (⨂[R] j, (⨂[R] i, V i j)) :=
  (sigmaRegroupLinearEquiv R (fun _ : I => J) (fun p => V p.1 p.2)).symm.trans
    (regroupLinearEquiv R (fun p : Σ _ : I, J => V p.1 p.2) sigmaSwap.symm)

@[simp]
theorem transposeLinearEquiv_tprod [Finite I] [Finite J] (x : ∀ i j, V i j) :
    transposeLinearEquiv R V (PiTensorProduct.tprod R (fun i =>
      PiTensorProduct.tprod R (x i))) =
      PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun i => x i j)) := by
  let y (p : Σ _ : I, J) := x p.1 p.2
  rw [transposeLinearEquiv, LinearEquiv.trans_apply,
    sigmaRegroupLinearEquiv_symm_tprod R (fun _ : I => J) (fun p => V p.1 p.2) y]
  exact regroupLinearEquiv_tprod R (fun p : Σ _ : I, J => V p.1 p.2) sigmaSwap.symm y

/-- An array of pure factors suffices to check equality of linear maps from a
nested indexed tensor product. -/
theorem nested_ext [Finite I] {W : Type uW} [AddCommMonoid W] [Module R W]
    {f g : (⨂[R] i, (⨂[R] j, V i j)) →ₗ[R] W}
    (h : ∀ x : ∀ i j, V i j,
      f (PiTensorProduct.tprod R (fun i => PiTensorProduct.tprod R (x i))) =
        g (PiTensorProduct.tprod R (fun i => PiTensorProduct.tprod R (x i)))) : f = g := by
  let q := sigmaRegroupLinearEquiv R (fun _ : I => J) (fun p => V p.1 p.2)
  have he : f.comp q.toLinearMap = g.comp q.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, q, sigmaRegroupLinearEquiv_tprod] using
        h (fun i j => x ⟨i, j⟩)
  exact LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := q.surjective y
    exact LinearMap.congr_fun he x

end Langlands.FiniteTensor

namespace Langlands.RestrictedTensor

variable (K : Type uR) [Field K] {ι : Type uI} {J : Type uJ} [Finite J]
variable {V : ι → J → Type uV}
variable [∀ i j, AddCommGroup (V i j)] [∀ i j, Module K (V i j)]
variable (E : Finset ι) (e : ∀ i j, V i j)

local notation "W" => (fun i => ⨂[K] j, V i j)
local notation "w" => (fun i => PiTensorProduct.tprod K (e i))
local notation "B" => (fun j => Space K (fun i => V i j) E (fun i => e i j))

private def blockRegroupStage (S : Index E) : Stage K W S.1 →ₗ[K] (⨂[K] j, B j) :=
  (PiTensorProduct.map (fun j => of K (fun i => V i j) E (fun i => e i j) S)).comp
    (FiniteTensor.transposeLinearEquiv K (fun i : S.1 => V i)).toLinearMap

private theorem blockRegroupStage_tprod (S : Index E) (x : ∀ (i : S.1) j, V i j) :
    blockRegroupStage K E e S (PiTensorProduct.tprod K (fun i =>
      PiTensorProduct.tprod K (x i))) =
      PiTensorProduct.tprod K (fun j => pure E (fun i => e i j) S (fun i => x i j)) := by
  simp only [blockRegroupStage, LinearMap.comp_apply, LinearEquiv.coe_coe,
    FiniteTensor.transposeLinearEquiv_tprod, PiTensorProduct.map_tprod, pure]

private theorem blockRegroupStage_transition {S T : Index E} (h : S ≤ T) :
    (blockRegroupStage K E e T).comp (transition w h) = blockRegroupStage K E e S := by
  refine FiniteTensor.nested_ext K (fun i : S.1 => V i)
    (f := (blockRegroupStage K E e T).comp (transition (K := K) w h))
    (g := blockRegroupStage K E e S) ?_
  intro x
  rw [LinearMap.comp_apply, transition_tprod, blockRegroupStage_tprod]
  have hx : extend w (T := T.1) (fun i => PiTensorProduct.tprod K (x i)) =
      fun i => PiTensorProduct.tprod K (fun j => extend (fun v => e v j) (fun v => x v j) i) := by
    funext i
    by_cases hi : i.1 ∈ S.1 <;> simp [extend, hi]
  rw [hx, blockRegroupStage_tprod]
  congr 1
  funext j
  exact pure_extend E (fun i => e i j) h (fun i => x i j)

/-- A restricted tensor of block tensors maps to the tensor of the corresponding
restricted products, with the same finite exceptional set. -/
def blockRegroup : Space K W E w →ₗ[K] (⨂[K] j, B j) :=
  DirectLimit.Module.lift K (Index E) _ (systemMap K W E w) (blockRegroupStage K E e)
    fun _ _ h x => LinearMap.congr_fun (blockRegroupStage_transition K E e h) x

@[simp]
theorem blockRegroup_pure (S : Index E) (x : ∀ (i : S.1) j, V i j) :
    blockRegroup K E e (pure E w S (fun i => PiTensorProduct.tprod K (x i))) =
      PiTensorProduct.tprod K (fun j => pure E (fun i => e i j) S (fun i => x i j)) := by
  exact blockRegroupStage_tprod K E e S x

private theorem blockRegroupStage_injective
    (he : ∀ i ∉ E, ∀ j, e i j ≠ 0) (S : Index E) :
    Function.Injective (blockRegroupStage K E e S) := by
  let q := fun j => of K (fun i => V i j) E (fun i => e i j) S
  have hq (j : J) : Function.Injective (q j) :=
    of_injective E (fun i => e i j) (fun i hi => he i hi j) S
  choose r hr using fun j => (q j).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hq j))
  have hleft : (PiTensorProduct.map r).comp (PiTensorProduct.map q) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp_rw [hr, PiTensorProduct.map_id]
  have hmap : Function.Injective (PiTensorProduct.map q) :=
    Function.LeftInverse.injective (fun x => LinearMap.congr_fun hleft x)
  exact hmap.comp (FiniteTensor.transposeLinearEquiv K (fun i : S.1 => V i)).injective

theorem blockRegroup_injective (he : ∀ i ∉ E, ∀ j, e i j ≠ 0) :
    Function.Injective (blockRegroup K E e) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨S, y, rfl⟩ := exists_of E w x
  change blockRegroupStage K E e S y = 0 at hx
  have hy := (injective_iff_map_eq_zero _).mp (blockRegroupStage_injective K E e he S) y hx
  rw [hy, map_zero]

theorem blockRegroup_surjective : Function.Surjective (blockRegroup K E e) := by
  let := Fintype.ofFinite J
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← PiTensorProduct.span_tprod_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨y, rfl⟩
  choose S z hz using fun j => exists_of E (fun i => e i j) (y j)
  let A : Index E := ⟨E ∪ Finset.univ.biUnion (fun j => (S j).1), Finset.subset_union_left⟩
  have hSA (j : J) : S j ≤ A := by
    intro i hi
    exact Finset.mem_union_right E (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩)
  let q := FiniteTensor.transposeLinearEquiv K (fun i : A.1 => V i)
  refine ⟨of K W E w A (q.symm (PiTensorProduct.tprod K (fun j =>
    transition (fun i => e i j) (hSA j) (z j)))), ?_⟩
  change (PiTensorProduct.map (fun j => of K (fun i => V i j) E (fun i => e i j) A))
    (q (q.symm _)) = _
  simp only [LinearEquiv.apply_symm_apply, PiTensorProduct.map_tprod, of_transition, ← hz]

/-- The restricted product of the placewise block tensors identifies with the
finite tensor of the blockwise restricted products. -/
def blockRegroupEquiv (he : ∀ i ∉ E, ∀ j, e i j ≠ 0) :
    Space K W E w ≃ₗ[K] (⨂[K] j, B j) :=
  LinearEquiv.ofBijective (blockRegroup K E e)
    ⟨blockRegroup_injective K E e he, blockRegroup_surjective K E e⟩

@[simp]
theorem blockRegroupEquiv_pure (he : ∀ i ∉ E, ∀ j, e i j ≠ 0)
    (S : Index E) (x : ∀ (i : S.1) j, V i j) :
    blockRegroupEquiv K E e he (pure E w S (fun i => PiTensorProduct.tprod K (x i))) =
      PiTensorProduct.tprod K (fun j => pure E (fun i => e i j) S (fun i => x i j)) :=
  blockRegroup_pure K E e S x

variable {V' : ι → J → Type uW}
variable [∀ i j, AddCommGroup (V' i j)] [∀ i j, Module K (V' i j)]

/-- Regrouping commutes with the blockwise maps at all places, using any common
finite bound for the failure to preserve the reference vectors. -/
theorem blockRegroup_mapWithBound
    (e' : ∀ i j, V' i j) (f : ∀ i j, V i j →ₗ[K] V' i j)
    (F : Finset ι) (hF : E ⊆ F) (hf : ∀ i ∉ F, ∀ j, f i j (e i j) = e' i j) :
    (blockRegroup K E e').comp
        (mapWithBound E E w (fun i => PiTensorProduct.tprod K (e' i))
          (fun i => PiTensorProduct.map (f i)) F hF (fun i hi => by
            rw [PiTensorProduct.map_tprod]
            exact congrArg (PiTensorProduct.tprod K) (funext (hf i hi)))) =
      (PiTensorProduct.map (fun j => mapWithBound E E (fun i => e i j) (fun i => e' i j)
        (fun i => f i j) F hF (fun i hi => hf i hi j))).comp (blockRegroup K E e) := by
  let m := mapWithBound E E w (fun i => PiTensorProduct.tprod K (e' i))
    (fun i => PiTensorProduct.map (f i)) F hF (fun i hi => by
      rw [PiTensorProduct.map_tprod]
      exact congrArg (PiTensorProduct.tprod K) (funext (hf i hi)))
  let m' := fun j => mapWithBound E E (fun i => e i j) (fun i => e' i j)
    (fun i => f i j) F hF (fun i hi => hf i hi j)
  let L := (blockRegroup K E e').comp m
  let R := (PiTensorProduct.map m').comp (blockRegroup K E e)
  change L = R
  refine hom_ext_cofinal (K := K) (V := W) (E := E) (e := w)
    (Y := ⨂[K] j, Space K (fun i => V' i j) E (fun i => e' i j)) (f := L) (g := R) F ?_
  intro S hS v
  have h : L.comp (of K W E w S) = R.comp (of K W E w S) := by
    refine FiniteTensor.nested_ext K (fun i : S.1 => V i)
      (f := L.comp (of K W E w S)) (g := R.comp (of K W E w S)) ?_
    intro x
    change blockRegroup K E e' (m (pure E w S (fun i => PiTensorProduct.tprod K (x i)))) =
      (PiTensorProduct.map m') (blockRegroup K E e
        (pure E w S (fun i => PiTensorProduct.tprod K (x i))))
    dsimp only [m]
    rw [mapWithBound_pure_of_subset _ _ _ _ _ _ _ _ _ hS]
    simp only [PiTensorProduct.map_tprod, blockRegroup_pure, m',
      mapWithBound_pure_of_subset _ _ _ _ _ _ _ _ _ hS]
  exact LinearMap.congr_fun h (PiTensorProduct.tprod K v)

end Langlands.RestrictedTensor
