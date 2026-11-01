import Langlands.Representation.RestrictedTensor.Maps

/-! # Reindexing the actual restricted tensor product -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uJ uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI} {κ : Type uJ}
variable {V : κ → Type uV}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]

/-- The bijection between a finite set and its image under an index equivalence. -/
abbrev reindexFinite (q : ι ≃ κ) (S : Finset ι) : S ≃ S.map q.toEmbedding where
  toFun i := ⟨q i, Finset.mem_map.mpr ⟨i, i.2, rfl⟩⟩
  invFun j := ⟨q.symm j, Finset.mem_map_equiv.mp j.2⟩
  left_inv i := Subtype.ext (q.symm_apply_apply i)
  right_inv j := Subtype.ext (q.apply_symm_apply j)

/-- Reindex a finite tensor stage using Mathlib's dependent tensor equivalence.
The inverse direction has a cast-free formula on elementary tensors. -/
def reindexStage (q : ι ≃ κ) (S : Finset ι) :
    Stage K (fun i => V (q i)) S ≃ₗ[K] Stage K V (S.map q.toEmbedding) :=
  (PiTensorProduct.reindex K (fun j : S.map q.toEmbedding => V j)
    (reindexFinite q S).symm).symm

@[simp]
theorem reindexStage_symm_tprod (q : ι ≃ κ) (S : Finset ι)
    (x : ∀ j : S.map q.toEmbedding, V j) :
    (reindexStage (K := K) (V := V) q S).symm (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K (fun i => x (reindexFinite q S i)) :=
  PiTensorProduct.reindex_tprod (reindexFinite q S).symm x

@[simp]
theorem reindexStage_tprod (q : ι ≃ κ) (S : Finset ι)
    (x : ∀ j : S.map q.toEmbedding, V j) :
    reindexStage (K := K) (V := V) q S
        (PiTensorProduct.tprod K (fun i => x (reindexFinite q S i))) =
      PiTensorProduct.tprod K x := by
  exact (congrArg (reindexStage (K := K) (V := V) q S)
    (reindexStage_symm_tprod q S x)).symm.trans
      ((reindexStage q S).apply_symm_apply _)

omit [∀ j, AddCommGroup (V j)] in
private theorem reindex_extend (q : ι ≃ κ) (e : ∀ j, V j)
    {S T : Finset ι} (x : ∀ j : S.map q.toEmbedding, V j) :
    (fun i : T =>
      extend e (T := T.map q.toEmbedding) x (reindexFinite q T i)) =
      extend (fun i => e (q i))
        (fun i : S => x (reindexFinite q S i)) := by
  funext i
  by_cases hi : i.1 ∈ S
  · simp [extend, hi, reindexFinite]
  · simp [extend, hi, reindexFinite]

/-- Reindexing commutes with adjoining the corresponding reference vectors. -/
theorem reindexStage_transition (q : ι ≃ κ) (e : ∀ j, V j)
    {S T : Finset ι} (h : S ⊆ T) :
    (reindexStage (K := K) (V := V) q T).toLinearMap.comp
        (transition (fun i => e (q i)) h) =
      (transition e (Finset.map_subset_map.mpr h)).comp
        (reindexStage q S).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (reindexStage (K := K) (V := V) q S).symm.surjective z
  apply (reindexStage (K := K) (V := V) q T).symm.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  have heq :
      (transition (fun i => e (q i)) h).comp
          (reindexStage (K := K) (V := V) q S).symm.toLinearMap =
        (reindexStage q T).symm.toLinearMap.comp
          (transition e (Finset.map_subset_map.mpr h)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change transition (fun i => e (q i)) h
        ((reindexStage q S).symm (PiTensorProduct.tprod K x)) =
      (reindexStage q T).symm
        (transition e (Finset.map_subset_map.mpr h) (PiTensorProduct.tprod K x))
    simp only [reindexStage_symm_tprod, transition_tprod]
    exact (transition_tprod (K := K) (fun i => e (q i)) h
      (fun i => x (reindexFinite q S i))).trans
        (congrArg (PiTensorProduct.tprod K) (reindex_extend q e (T := T) x).symm)
  exact LinearMap.congr_fun heq y

/-- Send each source finite stage to its actual image stage and descend through
the algebraic direct limit. No nonzero-reference assumption is needed here. -/
def reindexMap (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j) :
    Space K (fun i => V (q i)) E (fun i => e (q i)) →ₗ[K]
      Space K V (E.map q.toEmbedding) e :=
  lift E (fun i => e (q i))
    (fun S => (of K V (E.map q.toEmbedding) e
      ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩).comp
        (reindexStage q S.1).toLinearMap)
    (fun S T h x => by
      change of K V (E.map q.toEmbedding) e
          ⟨T.1.map q.toEmbedding, Finset.map_subset_map.mpr T.2⟩
        (reindexStage q T.1 (transition (fun i => e (q i)) h x)) =
          of K V (E.map q.toEmbedding) e
            ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩
              (reindexStage q S.1 x)
      have hc :
          reindexStage q T.1 (transition (fun i => e (q i)) h x) =
            transition e (Finset.map_subset_map.mpr h) (reindexStage q S.1 x) :=
        LinearMap.congr_fun (reindexStage_transition q e h) x
      exact (congrArg
        (of K V (E.map q.toEmbedding) e
          ⟨T.1.map q.toEmbedding, Finset.map_subset_map.mpr T.2⟩) hc).trans
        (of_transition (K := K) (E.map q.toEmbedding) e
          (S := ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩)
          (T := ⟨T.1.map q.toEmbedding, Finset.map_subset_map.mpr T.2⟩)
          (Finset.map_subset_map.mpr h) (reindexStage q S.1 x)))

@[simp]
theorem reindexMap_of (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j)
    (S : Index E) (x : Stage K (fun i => V (q i)) S.1) :
    reindexMap q E e (of K (fun i => V (q i)) E (fun i => e (q i)) S x) =
      of K V (E.map q.toEmbedding) e
        ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩
        (reindexStage q S.1 x) := rfl

@[simp]
theorem reindexMap_pure (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j)
    (S : Index E) (x : ∀ j : S.1.map q.toEmbedding, V j) :
    reindexMap (K := K) q E e
        (pure E (fun i => e (q i)) S
          (fun i => x (reindexFinite q S.1 i))) =
      pure (E.map q.toEmbedding) e
        ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩ x := by
  simp only [pure, reindexMap_of, reindexStage_tprod]

/-- The canonical reindexing map is injective for the usual nonzero-reference
restricted tensor product. -/
theorem reindexMap_injective (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j)
    (he : ∀ j ∉ E.map q.toEmbedding, e j ≠ 0) :
    Function.Injective (reindexMap (K := K) q E e) := by
  apply (reindexMap (K := K) q E e).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hz
  obtain ⟨S, y, rfl⟩ := exists_of E (fun i => e (q i)) x
  rw [reindexMap_of] at hz
  have hy : reindexStage q S.1 y = 0 :=
    (of_injective (E.map q.toEmbedding) e he _)
      (hz.trans (map_zero _).symm)
  have hy' : y = 0 :=
    (reindexStage (K := K) (V := V) q S.1).injective
      (hy.trans (map_zero _).symm)
  simp only [hy', map_zero]

private theorem exists_stage_of_eq (E : Finset κ) (e : ∀ j, V j)
    {S T : Index E} (h : S = T) (z : Stage K V T.1) :
    ∃ y : Stage K V S.1, of K V E e S y = of K V E e T z := by
  subst T
  exact ⟨z, rfl⟩

/-- Every target finite stage is the image of its inverse-index stage. -/
theorem reindexMap_surjective (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j) :
    Function.Surjective (reindexMap (K := K) q E e) := by
  intro x
  obtain ⟨T, z, rfl⟩ := exists_of (E.map q.toEmbedding) e x
  let S : Index E := ⟨T.1.map q.symm.toEmbedding, by
    intro i hi
    exact Finset.mem_map.mpr ⟨q i, T.2 (Finset.mem_map.mpr ⟨i, hi, rfl⟩),
      q.symm_apply_apply i⟩⟩
  have hST : S.1.map q.toEmbedding = T.1 := by
    simp [S, Finset.map_map]
  have hI :
      (⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩ :
        Index (E.map q.toEmbedding)) = T := Subtype.ext hST
  have hz : ∃ y : Stage K V (S.1.map q.toEmbedding),
      of K V (E.map q.toEmbedding) e
        ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩ y =
      of K V (E.map q.toEmbedding) e T z := by
    exact exists_stage_of_eq (E.map q.toEmbedding) e hI z
  obtain ⟨y, hy⟩ := hz
  refine ⟨of K (fun i => V (q i)) E (fun i => e (q i)) S
    ((reindexStage q S.1).symm y), ?_⟩
  rw [reindexMap_of, LinearEquiv.apply_symm_apply]
  exact hy

/-- A genuine linear equivalence of the actual restricted tensor spaces. -/
def reindex (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j)
    (he : ∀ j ∉ E.map q.toEmbedding, e j ≠ 0) :
    Space K (fun i => V (q i)) E (fun i => e (q i)) ≃ₗ[K]
      Space K V (E.map q.toEmbedding) e :=
  LinearEquiv.ofBijective (reindexMap q E e)
    ⟨reindexMap_injective q E e he, reindexMap_surjective q E e⟩

@[simp]
theorem reindex_apply (q : ι ≃ κ) (E : Finset ι) (e : ∀ j, V j)
    (he : ∀ j ∉ E.map q.toEmbedding, e j ≠ 0)
    (x : Space K (fun i => V (q i)) E (fun i => e (q i))) :
    reindex q E e he x = reindexMap q E e x := rfl

end Langlands.RestrictedTensor
