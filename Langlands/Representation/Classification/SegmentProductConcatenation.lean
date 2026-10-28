import Langlands.Representation.Classification.SegmentProductRefinement

/-! Concatenation of actual segment-product data over an ordered outer shape. -/

noncomputable section

namespace Langlands.FiniteConcatenation

private theorem finSigmaFinEquiv_castSucc {m : ℕ} (L : Fin (m + 1) → ℕ)
    (q : (i : Fin m) × Fin (L i.castSucc)) :
    finSigmaFinEquiv ⟨q.1.castSucc, q.2⟩ =
      Fin.cast (Fin.sum_univ_castSucc L).symm
        (Fin.castAdd (L (Fin.last m)) (finSigmaFinEquiv q)) := by
  apply Fin.ext
  simp only [finSigmaFinEquiv_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc]
  rfl

private theorem finSigmaFinEquiv_last {m : ℕ} (L : Fin (m + 1) → ℕ)
    (q : Fin (L (Fin.last m))) :
    finSigmaFinEquiv ⟨Fin.last m, q⟩ =
      Fin.cast (Fin.sum_univ_castSucc L).symm
        (Fin.natAdd (∑ i : Fin m, L i.castSucc) q) := by
  apply Fin.ext
  simp only [finSigmaFinEquiv_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_last]
  rfl

/-- Consecutive numbering of dependent finite fibers concatenates their lists. -/
theorem ofFn_finSigmaFinEquiv {α : Type*} {m : ℕ} (L : Fin m → ℕ)
    (f : ∀ i, Fin (L i) → α) :
    List.ofFn (fun k => f (finSigmaFinEquiv.symm k).1
      (finSigmaFinEquiv.symm k).2) =
      (List.ofFn (fun i => List.ofFn (f i))).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_congr (Fin.sum_univ_castSucc L), List.ofFn_add,
      List.ofFn_succ' (fun i => List.ofFn (f i)), List.concat_eq_append,
      List.flatten_concat]
    congr 1
    · rw [← ih (fun i => L i.castSucc) (fun i => f i.castSucc)]
      apply congrArg List.ofFn
      funext k
      obtain ⟨q, rfl⟩ := finSigmaFinEquiv.surjective k
      change f (finSigmaFinEquiv.symm (Fin.cast (Fin.sum_univ_castSucc L).symm
        (Fin.castAdd (L (Fin.last m)) (finSigmaFinEquiv q)))).1
        (finSigmaFinEquiv.symm (Fin.cast (Fin.sum_univ_castSucc L).symm
          (Fin.castAdd (L (Fin.last m)) (finSigmaFinEquiv q)))).2 = _
      rw [← finSigmaFinEquiv_castSucc L q, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
    · apply congrArg List.ofFn
      funext k
      rw [← finSigmaFinEquiv_last L k, Equiv.symm_apply_apply]

end Langlands.FiniteConcatenation

namespace Langlands.PadicField.TopologicalData.SegmentProductDatum

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  {n : ℕ} (D : BlockShape n)
  (a : ∀ k, SegmentProductDatum.{uV,uF} T (D.size k))

/-- Concatenate supplied actual inner data, retaining every occurrence and block. -/
def concatenate : SegmentProductDatum.{uV,uF} T n where
  length := ∑ k, (a k).length
  segments k := (a (finSigmaFinEquiv.symm k).1).segments (finSigmaFinEquiv.symm k).2
  degree_sum := (D.flatten (fun k => (a k).shape)).sum_eq
  blocks k := (a (finSigmaFinEquiv.symm k).1).blocks (finSigmaFinEquiv.symm k).2

@[simp]
theorem concatenate_shape :
    (concatenate D a).shape = D.flatten (fun k => (a k).shape) := rfl

/-- The complete concatenated list retains all supplied actual blocks in order. -/
theorem concatenate_blockList :
    (concatenate D a).blockList = (List.ofFn (fun k => (a k).blockList)).flatten :=
  FiniteConcatenation.ofFn_finSigmaFinEquiv (fun k => (a k).length)
    (fun k l => (a k).blockAt l)

/-- The segment list is the corresponding ordered concatenation. -/
theorem concatenate_segments :
    List.ofFn (concatenate D a).segments =
      (List.ofFn (fun k => List.ofFn (a k).segments)).flatten := by
  rw [← blockList_segments, concatenate_blockList, List.map_flatten]
  simp only [List.map_ofFn, Function.comp_def, blockList_segments]

/-- Concatenation inherits the strong socle property from all actual inner data. -/
theorem concatenate_hasSegmentSocles (ha : ∀ k, (a k).HasSegmentSocles) :
    (concatenate D a).HasSegmentSocles :=
  fun l => ha (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2

private theorem concatenate_size
    (q : (k : Fin D.length) × Fin (a k).length) :
    (a q.1).shape.size q.2 =
      ((concatenate D a).segments (D.flattenBlockEquiv (fun k => (a k).shape) q)).degree := by
  change ((a q.1).segments q.2).degree =
    ((a (finSigmaFinEquiv.symm (finSigmaFinEquiv q)).1).segments
      (finSigmaFinEquiv.symm (finSigmaFinEquiv q)).2).degree
  rw [Equiv.symm_apply_apply]

private theorem concatenate_refinementDatum (k : Fin D.length) :
    (concatenate D a).refinementDatum D (fun k => (a k).shape)
      (D.flattenBlockEquiv (fun k => (a k).shape))
      (concatenate_size D a) k = a k := by
  apply blockList_injective
  let E : ((k : Fin D.length) × Fin (a k).length) ≃ Fin (∑ k, (a k).length) :=
    finSigmaFinEquiv
  change List.ofFn (fun l =>
    (fun q : (k : Fin D.length) × Fin (a k).length => (a q.1).blockAt q.2)
      (E.symm (E ⟨k,l⟩))) = List.ofFn (a k).blockAt
  apply congrArg List.ofFn
  funext l
  exact congrArg (fun q : (k : Fin D.length) × Fin (a k).length =>
    (a q.1).blockAt q.2) (E.symm_apply_apply ⟨k,l⟩)

/-- Closed ordered regrouping identifies the outer product of the supplied actual
inner products with the actual concatenated flat product. -/
def concatenateInducedEquiv :
    letI := T.topology
    (T.normalizedProductInduced D
      (fun k => (a k).induced.representation)).Equiv
      (concatenate D a).induced.representation := by
  letI := T.topology
  let S : BlockRefinement D := fun k => (a k).shape
  let e := D.flattenBlockEquiv S
  let hs := concatenate_size D a
  have hc : ∀ k l (x : Fin ((S k).size l)),
      D.index k ((S k).index l x) =
        (concatenate D a).shape.index (e ⟨k,l⟩) (Fin.cast (hs ⟨k,l⟩) x) :=
    fun k l x => D.index_index_eq_flatten S ⟨k,l⟩ x
  let b : ∀ k,
      ((concatenate D a).refinementDatum D S e hs k).induced.representation.Equiv
        (a k).induced.representation :=
    fun k => inducedEquivOfBlockListEq _ _
      (congrArg blockList (concatenate_refinementDatum D a k))
  exact ((concatenate D a).refinementInducedEquiv D S e hs hc).trans
    (T.normalizedProductInducedEquiv D b) |>.symm

end Langlands.PadicField.TopologicalData.SegmentProductDatum
