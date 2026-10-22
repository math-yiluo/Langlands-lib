import Langlands.Representation.RestrictedTensor.Maps
import Mathlib.RingTheory.Flat.Basic

/-! # Finite-factor separation in the algebraic restricted tensor product -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uV uW

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
variable {V : ι → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Indices outside a finite family being separated. -/
abbrev Outside (A : Finset ι) := {i : ι // i ∉ A}

/-- The remaining indices of a finite stage, viewed in the complementary index type. -/
def tailSet (A S : Finset ι) : Finset (Outside A) :=
  S.subtype (fun i => i ∉ A)

@[simp]
theorem mem_tailSet (A S : Finset ι) (i : Outside A) :
    i ∈ tailSet A S ↔ i.1 ∈ S := Finset.mem_subtype

theorem tailSet_mono (A : Finset ι) {S T : Finset ι} (h : S ⊆ T) :
    tailSet A S ⊆ tailSet A T := Finset.subtype_mono h

/-- Swap the two finite-complement subtype conditions without changing the index. -/
def complementIndexEquiv (A S : Finset ι) :
    {i : S // i.1 ∉ A} ≃ tailSet A S where
  toFun i := ⟨⟨i.1.1, i.2⟩, Finset.mem_subtype.mpr i.1.2⟩
  invFun i := ⟨⟨i.1.1, Finset.mem_subtype.mp i.2⟩, i.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Finite-stage separation with the complementary factor indexed by `Outside A`. -/
def splitFinite {A S : Finset ι} (h : A ⊆ S) :
    Stage K V S ≃ₗ[K] Stage K V A ⊗[K] Stage K (fun i : Outside A => V i) (tailSet A S) :=
  (splitStage (K := K) (V := V) h).trans
    (TensorProduct.congr (LinearEquiv.refl K _)
      (PiTensorProduct.reindex K (fun i : {i : S // i.1 ∉ A} => V i.1)
        (complementIndexEquiv A S)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem splitFinite_tprod {A S : Finset ι} (h : A ⊆ S) (v : ∀ i : S, V i) :
    splitFinite (K := K) (V := V) h (PiTensorProduct.tprod K v) =
      (PiTensorProduct.tprod K (fun i : A => v ⟨i.1, h i.2⟩)) ⊗ₜ[K]
        PiTensorProduct.tprod K
          (fun i : tailSet A S => v ⟨i.1.1, Finset.mem_subtype.mp i.2⟩) := by
  simp only [splitFinite, LinearEquiv.trans_apply, splitStage_tprod,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  have hr := PiTensorProduct.reindex_tprod (R := K)
    (s := fun i : {i : S // i.1 ∉ A} => V i.1) (complementIndexEquiv A S)
    (fun i => v i.1)
  exact congrArg (fun x => (PiTensorProduct.tprod K (fun i : A => v ⟨i.1, h i.2⟩)) ⊗ₜ[K] x) hr

/-- Split a finite stage and send the complementary tensor into its actual limit. -/
def splitToTailStage {A : Finset ι} (e : ∀ i, V i) (S : Index A) :
    Stage K V S.1 →ₗ[K]
      Stage K V A ⊗[K] Space K (fun i : Outside A => V i) ∅ (fun i => e i) :=
  (TensorProduct.map LinearMap.id
    (of K (fun i : Outside A => V i) ∅ (fun i => e i)
      ⟨tailSet A S.1, Finset.empty_subset _⟩)).comp (splitFinite S.2).toLinearMap

@[simp]
theorem splitToTailStage_tprod {A : Finset ι} (e : ∀ i, V i) (S : Index A)
    (v : ∀ i : S.1, V i) :
    splitToTailStage e S (PiTensorProduct.tprod K v) =
      (PiTensorProduct.tprod K (fun i : A => v ⟨i.1, S.2 i.2⟩)) ⊗ₜ[K]
        pure ∅ (fun i : Outside A => e i) ⟨tailSet A S.1, Finset.empty_subset _⟩
          (fun i => v ⟨i.1.1, Finset.mem_subtype.mp i.2⟩) := by
  simp [splitToTailStage, pure]

/-- Splitting is compatible with every adjoining-reference transition. -/
theorem splitToTailStage_transition {A : Finset ι} (e : ∀ i, V i)
    {S T : Index A} (h : S ≤ T) :
    (splitToTailStage (K := K) e T).comp (transition e h) = splitToTailStage e S := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change splitToTailStage e T (transition e h (PiTensorProduct.tprod K v)) =
    splitToTailStage e S (PiTensorProduct.tprod K v)
  rw [transition_tprod, splitToTailStage_tprod, splitToTailStage_tprod]
  rw [← pure_extend ∅ (fun i : Outside A => e i)
    (S := ⟨tailSet A S.1, Finset.empty_subset _⟩)
    (T := ⟨tailSet A T.1, Finset.empty_subset _⟩) (tailSet_mono A h)]
  congr 2
  · funext i
    simp [extend, S.2 i.2]
  · funext i
    by_cases hi : i.1.1 ∈ S.1
    · have hi' : i.1 ∈ tailSet A S.1 := (mem_tailSet A S.1 i.1).mpr hi
      simp only [extend, dite_eq_left hi, dite_eq_left hi']
    · have hi' : i.1 ∉ tailSet A S.1 := fun hi' => hi ((mem_tailSet A S.1 i.1).mp hi')
      simp only [extend, dite_eq_right hi, dite_eq_right hi']

/-- The linear splitting map on the full limit, initially with exceptional set `A`. -/
def splitToTail (A : Finset ι) (e : ∀ i, V i) :
    Space K V A e →ₗ[K]
      Stage K V A ⊗[K] Space K (fun i : Outside A => V i) ∅ (fun i => e i) :=
  lift A e (splitToTailStage e)
    (fun _ _ h x => LinearMap.congr_fun (splitToTailStage_transition e h) x)

@[simp]
theorem splitToTail_pure (A : Finset ι) (e : ∀ i, V i) (S : Index A)
    (v : ∀ i : S.1, V i) :
    splitToTail A e (pure A e S v) =
      (PiTensorProduct.tprod K (fun i : A => v ⟨i.1, S.2 i.2⟩)) ⊗ₜ[K]
        pure ∅ (fun i : Outside A => e i) ⟨tailSet A S.1, Finset.empty_subset _⟩
          (fun i => v ⟨i.1.1, Finset.mem_subtype.mp i.2⟩) := by
  simp [splitToTail, pure]

/-- A change of the finite exceptional set fixes elementary tensors on common stages. -/
theorem change_same_pure (E E' : Finset ι) (e : ∀ i, V i)
    (S : Index E) (hS : E' ⊆ S.1) (v : ∀ i : S.1, V i) :
    change (K := K) E E' e e (Filter.Eventually.of_forall fun _ => rfl) (pure E e S v) =
      pure E' e ⟨S.1, hS⟩ v :=
  map_pure_of_preserves E E' e e (fun _ => LinearMap.id) _ S hS (fun _ _ => rfl) v

/-- Split at `A`, retaining precisely the original exceptional indices outside `A`
in the complementary restricted tensor product. -/
def splitWithExceptions (E A : Finset ι) (e : ∀ i, V i) :
    Space K V (E ∪ A) e →ₗ[K]
      Stage K V A ⊗[K] Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i) :=
  (TensorProduct.map LinearMap.id
    (change ∅ (tailSet A E) (fun i : Outside A => e i) (fun i => e i)
      (Filter.Eventually.of_forall fun _ => rfl)).toLinearMap).comp
    ((splitToTail A e).comp
      (change (E ∪ A) A e e (Filter.Eventually.of_forall fun _ => rfl)).toLinearMap)

@[simp]
theorem splitWithExceptions_pure (E A : Finset ι) (e : ∀ i, V i)
    (S : Index (E ∪ A)) (v : ∀ i : S.1, V i) :
    splitWithExceptions E A e (pure (E ∪ A) e S v) =
      (PiTensorProduct.tprod K
        (fun i : A => v ⟨i.1, S.2 (Finset.mem_union_right E i.2)⟩)) ⊗ₜ[K]
        pure (tailSet A E) (fun i : Outside A => e i)
          ⟨tailSet A S.1, tailSet_mono A (Finset.subset_union_left.trans S.2)⟩
          (fun i => v ⟨i.1.1, Finset.mem_subtype.mp i.2⟩) := by
  simp only [splitWithExceptions, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [change_same_pure _ _ _ S (Finset.subset_union_right.trans S.2)]
  rw [splitToTail_pure, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
  rw [change_same_pure _ _ _ _ (tailSet_mono A (Finset.subset_union_left.trans S.2))]

/-- The full splitting restricted to a finite stage is the finite splitting followed
by the injective inclusion of its complementary stage. -/
theorem splitWithExceptions_of (E A : Finset ι) (e : ∀ i, V i)
    (S : Index (E ∪ A)) :
    (splitWithExceptions (K := K) E A e).comp (of K V (E ∪ A) e S) =
      (TensorProduct.map LinearMap.id
        (of K (fun i : Outside A => V i) (tailSet A E) (fun i => e i)
          ⟨tailSet A S.1, tailSet_mono A (Finset.subset_union_left.trans S.2)⟩)).comp
        (splitFinite (Finset.subset_union_right.trans S.2)).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change splitWithExceptions (K := K) E A e (pure (E ∪ A) e S v) = _
  rw [splitWithExceptions_pure]
  simp [splitFinite_tprod, pure]

/-- Nonzero reference vectors make full-limit splitting injective, also for
infinite-dimensional local vector spaces. -/
theorem splitWithExceptions_injective (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) :
    Function.Injective (splitWithExceptions (K := K) E A e) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨S, y, rfl⟩ := exists_of (E ∪ A) e x
  have htail : Function.Injective
      (of K (fun i : Outside A => V i) (tailSet A E) (fun i => e i)
        ⟨tailSet A S.1, tailSet_mono A (Finset.subset_union_left.trans S.2)⟩) :=
    of_injective (tailSet A E) (fun i : Outside A => e i)
      (fun i hi => he i.1 (fun hiE => hi ((mem_tailSet A E i).mpr hiE))) _
  have hmap := TensorProduct.map_injective_of_flat_flat
    (LinearMap.id : Stage K V A →ₗ[K] Stage K V A) _ Function.injective_id htail
  have hsplit := hmap.comp (splitFinite (K := K) (V := V)
    (Finset.subset_union_right.trans S.2)).injective
  have hy : y = 0 := hsplit (by
    have hz := (LinearMap.congr_fun (splitWithExceptions_of (K := K) E A e S) y).symm.trans hx
    simpa only [Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hz)
  simp [hy]

/-- Combine the separated finite family with a finite family of complementary indices. -/
def joinSet (A : Finset ι) (B : Finset (Outside A)) : Finset ι :=
  A ∪ B.map (Function.Embedding.subtype _)

@[simp]
theorem mem_joinSet (A : Finset ι) (B : Finset (Outside A)) (i : Outside A) :
    i.1 ∈ joinSet A B ↔ i ∈ B := by
  constructor
  · intro hi
    obtain hi | hi := Finset.mem_union.mp hi
    · exact (i.2 hi).elim
    · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
      have hji' : j = i := Subtype.ext hji
      simpa only [hji'] using hj
  · intro hi
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨i, hi, rfl⟩)

@[simp]
theorem tailSet_joinSet (A : Finset ι) (B : Finset (Outside A)) :
    tailSet A (joinSet A B) = B := by
  ext i
  exact (mem_tailSet A _ i).trans (mem_joinSet A B i)

theorem joinSet_contains (E A : Finset ι) (B : Index (tailSet A E)) :
    E ∪ A ⊆ joinSet A B.1 := by
  intro i hi
  by_cases hiA : i ∈ A
  · exact Finset.mem_union_left _ hiA
  · have hiE : i ∈ E := (Finset.mem_union.mp hi).resolve_right hiA
    exact (mem_joinSet A B.1 ⟨i, hiA⟩).mpr
      (B.2 ((mem_tailSet A E ⟨i, hiA⟩).mpr hiE))

/-- Assemble two disjoint families of coordinates into their combined finite stage. -/
def joinVector (A : Finset ι) (B : Finset (Outside A))
    (v : ∀ i : A, V i) (w : ∀ i : B, V i.1) :
    ∀ i : joinSet A B, V i := fun i =>
  if hi : i.1 ∈ A then v ⟨i.1, hi⟩
  else w ⟨⟨i.1, hi⟩, (mem_joinSet A B ⟨i.1, hi⟩).mp i.2⟩

omit [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] in
@[simp]
theorem joinVector_left (A : Finset ι) (B : Finset (Outside A))
    (v : ∀ i : A, V i) (w : ∀ i : B, V i.1) (i : A) :
    joinVector A B v w ⟨i.1, Finset.mem_union_left _ i.2⟩ = v i := by
  simp [joinVector, i.2]

omit [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] in
@[simp]
theorem joinVector_right (A : Finset ι) (B : Finset (Outside A))
    (v : ∀ i : A, V i) (w : ∀ i : B, V i.1) (i : B) :
    joinVector A B v w ⟨i.1.1, (mem_joinSet A B i.1).mpr i.2⟩ = w i := by
  simp [joinVector, i.1.2]

/-- Reassembling finite elementary coordinates and splitting them gives the prescribed
finite tensor and complementary elementary tensor exactly. -/
theorem splitWithExceptions_joinVector (E A : Finset ι) (e : ∀ i, V i)
    (B : Index (tailSet A E)) (v : ∀ i : A, V i) (w : ∀ i : B.1, V i.1) :
    splitWithExceptions (K := K) E A e
      (pure (E ∪ A) e ⟨joinSet A B.1, joinSet_contains E A B⟩ (joinVector A B.1 v w)) =
      (PiTensorProduct.tprod K v) ⊗ₜ[K] pure (tailSet A E) (fun i : Outside A => e i) B w := by
  rw [splitWithExceptions_pure]
  congr 1
  · congr 1
    funext i
    exact joinVector_left A B.1 v w i
  · apply (of_eq_iff (tailSet A E) (fun i : Outside A => e i) _ _).mpr
    refine ⟨B, (tailSet_joinSet A B.1).le, le_rfl, ?_⟩
    simp only [transition_tprod, extend_self]
    congr 1
    funext i
    have hi : i.1 ∈ tailSet A (joinSet A B.1) := by
      rw [tailSet_joinSet]
      exact i.2
    simp only [extend, dite_eq_left hi]
    exact joinVector_right A B.1 v w i

/-- Every tensor of a finite factor and a complementary restricted tensor has a
reassembly in the original restricted tensor space. -/
theorem splitWithExceptions_surjective (E A : Finset ι) (e : ∀ i, V i) :
    Function.Surjective (splitWithExceptions (K := K) E A e) := by
  let R := (splitWithExceptions (K := K) E A e).range
  have hpure (v : ∀ i : A, V i) (B : Index (tailSet A E)) (w : ∀ i : B.1, V i.1) :
      (PiTensorProduct.tprod K v) ⊗ₜ[K] pure (tailSet A E) (fun i : Outside A => e i) B w ∈ R :=
    ⟨_, splitWithExceptions_joinVector E A e B v w⟩
  have hleft (v : ∀ i : A, V i)
      (y : Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i)) :
      (PiTensorProduct.tprod K v) ⊗ₜ[K] y ∈ R := by
    induction y using Langlands.RestrictedTensor.induction with
    | hpure B w => exact hpure v B w
    | hadd y z hy hz => simpa only [TensorProduct.tmul_add] using R.add_mem hy hz
    | hsmul a y hy => simpa only [TensorProduct.tmul_smul] using R.smul_mem a hy
  have htmul (x : Stage K V A)
      (y : Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i)) :
      x ⊗ₜ[K] y ∈ R := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simpa only [TensorProduct.smul_tmul'] using R.smul_mem a (hleft v y)
    | add x z hx hz => simpa only [TensorProduct.add_tmul] using R.add_mem hx hz
  intro z
  have hz : z ∈ R := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact htmul x y
    | add x y hx hy => exact R.add_mem hx hy
  exact hz

/-- Canonical finite-factor separation in the full restricted tensor product.
The complement retains the original exceptional indices outside `A`. -/
def finiteSeparation (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) :
    Space K V E e ≃ₗ[K]
      Stage K V A ⊗[K] Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i) :=
  (change E (E ∪ A) e e (Filter.Eventually.of_forall fun _ => rfl)).trans
    (LinearEquiv.ofBijective (splitWithExceptions E A e)
      ⟨splitWithExceptions_injective E A e he, splitWithExceptions_surjective E A e⟩)

@[simp]
theorem finiteSeparation_pure (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) (S : Index E) (hA : A ⊆ S.1) (v : ∀ i : S.1, V i) :
    finiteSeparation E A e he (pure E e S v) =
      (PiTensorProduct.tprod K (fun i : A => v ⟨i.1, hA i.2⟩)) ⊗ₜ[K]
        pure (tailSet A E) (fun i : Outside A => e i)
          ⟨tailSet A S.1, tailSet_mono A S.2⟩
          (fun i => v ⟨i.1.1, Finset.mem_subtype.mp i.2⟩) := by
  change splitWithExceptions (K := K) E A e
    (change E (E ∪ A) e e (Filter.Eventually.of_forall fun _ => rfl) (pure E e S v)) = _
  rw [change_same_pure _ _ _ _ (Finset.union_subset S.2 hA)]
  exact splitWithExceptions_pure E A e ⟨S.1, Finset.union_subset S.2 hA⟩ v

theorem finiteSeparation_joinVector (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) (B : Index (tailSet A E))
    (v : ∀ i : A, V i) (w : ∀ i : B.1, V i.1) :
    finiteSeparation (K := K) E A e he
      (pure E e ⟨joinSet A B.1, Finset.subset_union_left.trans (joinSet_contains E A B)⟩
        (joinVector A B.1 v w)) =
      (PiTensorProduct.tprod K v) ⊗ₜ[K] pure (tailSet A E) (fun i : Outside A => e i) B w := by
  change splitWithExceptions (K := K) E A e
    (change E (E ∪ A) e e (Filter.Eventually.of_forall fun _ => rfl)
      (pure E e ⟨joinSet A B.1, Finset.subset_union_left.trans (joinSet_contains E A B)⟩
        (joinVector A B.1 v w))) = _
  rw [change_same_pure _ _ _ _ (joinSet_contains E A B)]
  exact splitWithExceptions_joinVector E A e B v w

/-- Reassembly is the actual inverse of the proved finite-factor separation. -/
def reassemble (E A : Finset ι) (e : ∀ i, V i) (he : ∀ i ∉ E, e i ≠ 0) :
    (Stage K V A ⊗[K] Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i))
      ≃ₗ[K] Space K V E e :=
  (finiteSeparation (K := K) E A e he).symm

@[simp]
theorem reassemble_separate (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) (x : Space K V E e) :
    reassemble (K := K) E A e he (finiteSeparation E A e he x) = x :=
  (finiteSeparation E A e he).symm_apply_apply x

@[simp]
theorem separate_reassemble (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0)
    (y : Stage K V A ⊗[K] Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i)) :
    finiteSeparation E A e he (reassemble E A e he y) = y :=
  (finiteSeparation E A e he).apply_symm_apply y

/-- The inverse equivalence has the expected elementary reassembly formula. -/
theorem reassemble_tmul_pure (E A : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) (B : Index (tailSet A E))
    (v : ∀ i : A, V i) (w : ∀ i : B.1, V i.1) :
    reassemble E A e he
      ((PiTensorProduct.tprod K v) ⊗ₜ[K] pure (tailSet A E) (fun i : Outside A => e i) B w) =
      pure E e ⟨joinSet A B.1, Finset.subset_union_left.trans (joinSet_contains E A B)⟩
        (joinVector A B.1 v w) := by
  apply (finiteSeparation E A e he).injective
  rw [separate_reassemble, finiteSeparation_joinVector]

/-- Change which finite set of factors is exposed, by reassembly and separation. -/
def regroup (E A B : Finset ι) (e : ∀ i, V i) (he : ∀ i ∉ E, e i ≠ 0) :
    (Stage K V A ⊗[K] Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i)) ≃ₗ[K]
      (Stage K V B ⊗[K] Space K (fun i : Outside B => V i) (tailSet B E) (fun i => e i)) :=
  (reassemble (K := K) E A e he).trans (finiteSeparation E B e he)

@[simp]
theorem regroup_refl (E A : Finset ι) (e : ∀ i, V i) (he : ∀ i ∉ E, e i ≠ 0) :
    regroup (K := K) E A A e he = LinearEquiv.refl K _ := by
  unfold regroup reassemble
  exact LinearEquiv.symm_trans_self (finiteSeparation E A e he)

/-- Successive finite regroupings agree with the direct regrouping. -/
theorem regroup_trans (E A B C : Finset ι) (e : ∀ i, V i) (he : ∀ i ∉ E, e i ≠ 0) :
    (regroup (K := K) E A B e he).trans (regroup E B C e he) = regroup E A C e he := by
  unfold regroup reassemble
  rw [LinearEquiv.trans_assoc, LinearEquiv.trans_symm_cancel_left]

@[simp]
theorem regroup_separate (E A B : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) (x : Space K V E e) :
    regroup (K := K) E A B e he (finiteSeparation E A e he x) = finiteSeparation E B e he x := by
  simp only [regroup, reassemble, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- Expose an individual local vector space, not merely its singleton tensor model. -/
def localSeparation (E : Finset ι) (i : ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) :
    Space K V E e ≃ₗ[K]
      V i ⊗[K] Space K (fun j : Outside {i} => V j) (tailSet {i} E) (fun j => e j) :=
  (finiteSeparation E {i} e he).trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv (R := K)
      (s := fun j : ({i} : Finset ι) => V j) ⟨i, Finset.mem_singleton_self i⟩)
      (LinearEquiv.refl K _))

@[simp]
theorem localSeparation_pure (E : Finset ι) (i : ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, e i ≠ 0) (S : Index E) (hi : i ∈ S.1) (v : ∀ j : S.1, V j) :
    localSeparation E i e he (pure E e S v) =
      v ⟨i, hi⟩ ⊗ₜ[K]
        pure (tailSet {i} E) (fun j : Outside {i} => e j)
          ⟨tailSet {i} S.1, tailSet_mono {i} S.2⟩
          (fun j => v ⟨j.1.1, Finset.mem_subtype.mp j.2⟩) := by
  simp only [localSeparation, LinearEquiv.trans_apply,
    finiteSeparation_pure E {i} e he S (Finset.singleton_subset_iff.mpr hi),
    TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod,
    LinearEquiv.refl_apply]

/-- Restrict the prescribed nonzero reference data to the complementary index type. -/
def ReferenceVectors.tail {E : Finset ι} (r : ReferenceVectors V E) (A : Finset ι) :
    ReferenceVectors (fun i : Outside A => V i) (tailSet A E) where
  vector i hi := r.vector i (fun hiE => hi ((mem_tailSet A E i).mpr hiE))
  nonzero i hi := r.nonzero i (fun hiE => hi ((mem_tailSet A E i).mpr hiE))

theorem ReferenceVectors.tail_family {E : Finset ι} (r : ReferenceVectors V E) (A : Finset ι) :
    (r.tail A).family = fun i : Outside A => r.family i := by
  funext i
  by_cases hi : i.1 ∈ E
  · have hi' : i ∈ tailSet A E := (mem_tailSet A E i).mpr hi
    simp [ReferenceVectors.family, hi, hi']
  · have hi' : i ∉ tailSet A E := fun h => hi ((mem_tailSet A E i).mp h)
    simp [ReferenceVectors.family, hi, hi', ReferenceVectors.tail]

/-- Finite-factor separation with nonzero-reference `Product` on both sides. -/
def productSeparation (E A : Finset ι) (r : ReferenceVectors V E) :
    Product K V E r ≃ₗ[K]
      Stage K V A ⊗[K] Product K (fun i : Outside A => V i) (tailSet A E) (r.tail A) := by
  change Space K V E r.family ≃ₗ[K]
    Stage K V A ⊗[K] Space K (fun i : Outside A => V i) (tailSet A E) (r.tail A).family
  rw [ReferenceVectors.tail_family]
  exact finiteSeparation E A r.family r.family_nonzero

variable {W : ι → Type uW}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- Cofinite reference preservation remains cofinite on a complementary index set. -/
theorem tail_preserves (A : Finset ι) {e : ∀ i, V i} {e' : ∀ i, W i}
    {f : ∀ i, V i →ₗ[K] W i} (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    ∀ᶠ i : Outside A in Filter.cofinite, f i (e i) = e' i :=
  (tailSet A (mapBound ∅ hf)).eventually_cofinite_notMem.mono fun i hi =>
    mapBound_preserves ∅ hf i (fun h => hi ((mem_tailSet A _ i).mpr h))

/-- Finite-factor separation is natural for all almost-everywhere
reference-preserving component maps, including changes of exceptional sets. -/
theorem finiteSeparation_natural (E E' A : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (he : ∀ i ∉ E, e i ≠ 0) (he' : ∀ i ∉ E', e' i ≠ 0)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    (finiteSeparation E' A e' he').toLinearMap.comp (map E E' e e' f hf) =
      (TensorProduct.map (PiTensorProduct.map (fun i : A => f i))
        (map (tailSet A E) (tailSet A E') (fun i : Outside A => e i) (fun i => e' i)
          (fun i => f i) (tail_preserves A hf))).comp
        (finiteSeparation E A e he).toLinearMap := by
  apply hom_ext_cofinal (A ∪ mapBound E' hf)
  intro S hS v
  have hA : A ⊆ S.1 := Finset.subset_union_left.trans hS
  have hB : mapBound E' hf ⊆ S.1 := Finset.subset_union_right.trans hS
  have hE' : E' ⊆ S.1 := (subset_mapBound E' hf).trans hB
  have hp : ∀ i ∉ S.1, f i (e i) = e' i :=
    fun i hi => mapBound_preserves E' hf i (fun h => hi (hB h))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_pure_of_preserves E E' e e' f hf S hE' hp]
  rw [finiteSeparation_pure E' A e' he' ⟨S.1, hE'⟩ hA]
  rw [finiteSeparation_pure E A e he S hA, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rw [map_pure_of_preserves (tailSet A E) (tailSet A E')
    (fun i : Outside A => e i) (fun i => e' i) (fun i => f i) (tail_preserves A hf)
    ⟨tailSet A S.1, tailSet_mono A S.2⟩ (tailSet_mono A hE')
    (fun i hi => hp i (fun h => hi ((mem_tailSet A S.1 i).mpr h)))]

/-- The inverse reassembly obeys the same component-map naturality square. -/
theorem reassemble_natural (E E' A : Finset ι) (e : ∀ i, V i) (e' : ∀ i, W i)
    (he : ∀ i ∉ E, e i ≠ 0) (he' : ∀ i ∉ E', e' i ≠ 0)
    (f : ∀ i, V i →ₗ[K] W i) (hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i) :
    (map E E' e e' f hf).comp (reassemble E A e he).toLinearMap =
      (reassemble E' A e' he').toLinearMap.comp
        (TensorProduct.map (PiTensorProduct.map (fun i : A => f i))
          (map (tailSet A E) (tailSet A E') (fun i : Outside A => e i) (fun i => e' i)
            (fun i => f i) (tail_preserves A hf))) := by
  apply LinearMap.ext
  intro x
  apply (finiteSeparation E' A e' he').injective
  have h := LinearMap.congr_fun (finiteSeparation_natural E E' A e e' he he' f hf)
    (reassemble E A e he x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, separate_reassemble] using h

end Langlands.RestrictedTensor
