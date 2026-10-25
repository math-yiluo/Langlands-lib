import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-! # Ordered composition of two block refinements -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open Geometric

variable {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q))

/-- Pull the refinement of a flattened middle block back to its original rank.
Only the total-rank proof changes; lengths, sizes and their order are retained. -/
def refinementWithin (i : Fin B.length) : BlockRefinement (Q i) := fun j =>
  { length := (R (B.flattenBlockEquiv Q ⟨i, j⟩)).length
    size := (R (B.flattenBlockEquiv Q ⟨i, j⟩)).size
    positive := (R (B.flattenBlockEquiv Q ⟨i, j⟩)).positive
    sum_eq := (R (B.flattenBlockEquiv Q ⟨i, j⟩)).sum_eq.trans
      (B.flatten_size_flattenBlockEquiv Q ⟨i, j⟩) }

/-- Concatenate the fine refinements of the middle blocks inside each outer block. -/
def composeRefinement : BlockRefinement B := fun i =>
  (Q i).flatten (B.refinementWithin Q R i)

/-- A fine block is labelled by its outer, middle and fine block numbers. -/
abbrev RefinementTriple :=
  (i : Fin B.length) × (j : Fin (Q i).length) ×
    Fin (R (B.flattenBlockEquiv Q ⟨i, j⟩)).length

/-- Number the triples by flattening the outer and middle blocks first. -/
def nestedFlattenBlockEquiv : B.RefinementTriple Q R ≃
    Fin ((B.flatten Q).flatten R).length :=
  ((Equiv.sigmaAssoc fun i j => Fin (R (B.flattenBlockEquiv Q ⟨i, j⟩)).length).symm.trans
    (Equiv.sigmaCongrLeft (β := fun k => Fin (R k).length) (B.flattenBlockEquiv Q))).trans
      ((B.flatten Q).flattenBlockEquiv R)

/-- Number the triples by flattening the middle and fine blocks first. -/
def composedFlattenBlockEquiv : B.RefinementTriple Q R ≃
    Fin (B.flatten (B.composeRefinement Q R)).length :=
  (Equiv.sigmaCongrRight fun i =>
    (Q i).flattenBlockEquiv (B.refinementWithin Q R i)).trans
      (B.flattenBlockEquiv (B.composeRefinement Q R))

@[simp] theorem nestedFlattenBlockEquiv_apply (p : B.RefinementTriple Q R) :
    B.nestedFlattenBlockEquiv Q R p =
      (B.flatten Q).flattenBlockEquiv R ⟨B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩, p.2.2⟩ := rfl

@[simp] theorem composedFlattenBlockEquiv_apply (p : B.RefinementTriple Q R) :
    B.composedFlattenBlockEquiv Q R p =
      B.flattenBlockEquiv (B.composeRefinement Q R)
        ⟨p.1, (Q p.1).flattenBlockEquiv (B.refinementWithin Q R p.1) p.2⟩ := rfl

/-- Both ordered concatenations have the same number of fine blocks. -/
theorem flatten_composeRefinement_length :
    ((B.flatten Q).flatten R).length = (B.flatten (B.composeRefinement Q R)).length := by
  have h := Fintype.card_congr
    ((B.nestedFlattenBlockEquiv Q R).symm.trans (B.composedFlattenBlockEquiv Q R))
  simpa only [Fintype.card_fin] using h

private theorem composedBlock_lt_of_nestedBlock_lt (p p' : B.RefinementTriple Q R)
    (h : B.nestedFlattenBlockEquiv Q R p < B.nestedFlattenBlockEquiv Q R p') :
    B.composedFlattenBlockEquiv Q R p < B.composedFlattenBlockEquiv Q R p' := by
  rcases p with ⟨i, j, l⟩
  rcases p' with ⟨i', j', l'⟩
  change (B.flatten Q).flattenBlockEquiv R ⟨B.flattenBlockEquiv Q ⟨i, j⟩, l⟩ <
    (B.flatten Q).flattenBlockEquiv R ⟨B.flattenBlockEquiv Q ⟨i', j'⟩, l'⟩ at h
  rcases ((B.flatten Q).flattenBlockEquiv_lt_iff R _ _).mp h with hmid | ⟨hmid, hfine⟩
  · rcases (B.flattenBlockEquiv_lt_iff Q _ _).mp hmid with hi | ⟨hi, hj⟩
    · exact (B.flattenBlockEquiv_lt_iff (B.composeRefinement Q R) _ _).mpr (Or.inl hi)
    · change i = i' at hi
      subst i'
      apply (B.flattenBlockEquiv_lt_iff (B.composeRefinement Q R) _ _).mpr
      refine Or.inr ⟨rfl, ?_⟩
      exact (Q i).flattenBlockEquiv_lt_iff (B.refinementWithin Q R i) _ _ |>.mpr
        (Or.inl (show j < j' from hj))
  · have hpair := (B.flattenBlockEquiv Q).injective hmid
    have hi := congrArg Sigma.fst hpair
    change i = i' at hi
    subst i'
    have hj : j = j' := eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
    subst j'
    apply (B.flattenBlockEquiv_lt_iff (B.composeRefinement Q R) _ _).mpr
    refine Or.inr ⟨rfl, ?_⟩
    exact (Q i).flattenBlockEquiv_lt_iff (B.refinementWithin Q R i) _ _ |>.mpr
      (Or.inr ⟨rfl, hfine⟩)

/-- The two routes give literally the same consecutive block number, after the
necessary cast between the equal block counts. -/
theorem flatten_composeRefinement_block (p : B.RefinementTriple Q R) :
    Fin.cast (B.flatten_composeRefinement_length Q R) (B.nestedFlattenBlockEquiv Q R p) =
      B.composedFlattenBlockEquiv Q R p := by
  let e := B.nestedFlattenBlockEquiv Q R
  let f := B.composedFlattenBlockEquiv Q R
  let H : Fin ((B.flatten Q).flatten R).length → Fin ((B.flatten Q).flatten R).length :=
    fun k => Fin.cast (B.flatten_composeRefinement_length Q R).symm (f (e.symm k))
  have hmono : StrictMono H := by
    intro k k' hkk'
    have h := B.composedBlock_lt_of_nestedBlock_lt Q R (e.symm k) (e.symm k')
      (by simpa only [e, Equiv.apply_symm_apply] using hkk')
    exact h
  have hfix : H (e p) = e p := le_antisymm hmono.apply_le hmono.le_apply
  have hval := congrArg Fin.val hfix
  apply Fin.ext
  simpa only [H, Fin.val_cast, Equiv.symm_apply_apply] using hval.symm

/-- The fine-block rank on the route through the middle flattened shape. -/
theorem nestedFlatten_size (p : B.RefinementTriple Q R) :
    ((B.flatten Q).flatten R).size (B.nestedFlattenBlockEquiv Q R p) =
      (R (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)).size p.2.2 :=
  (B.flatten Q).flatten_size_flattenBlockEquiv R _

/-- The fine-block rank on the route through the composite refinement. -/
theorem composedFlatten_size (p : B.RefinementTriple Q R) :
    (B.flatten (B.composeRefinement Q R)).size (B.composedFlattenBlockEquiv Q R p) =
      (R (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)).size p.2.2 := by
  calc
    _ = (B.composeRefinement Q R p.1).size
        ((Q p.1).flattenBlockEquiv (B.refinementWithin Q R p.1) p.2) :=
      B.flatten_size_flattenBlockEquiv (B.composeRefinement Q R) _
    _ = _ := (Q p.1).flatten_size_flattenBlockEquiv (B.refinementWithin Q R p.1) p.2

/-- Every fine block has exactly the same rank on the two routes, with its block
number transported by the proved equality of block counts. -/
theorem flatten_composeRefinement_size (k : Fin ((B.flatten Q).flatten R).length) :
    ((B.flatten Q).flatten R).size k =
      (B.flatten (B.composeRefinement Q R)).size
        (Fin.cast (B.flatten_composeRefinement_length Q R) k) := by
  obtain ⟨p, rfl⟩ := (B.nestedFlattenBlockEquiv Q R).surjective k
  rw [B.flatten_composeRefinement_block Q R p,
    B.nestedFlatten_size Q R p, B.composedFlatten_size Q R p]

/-- Ordered flattening is exactly associative as an equality of block-shape
structures, not merely up to a permutation of their blocks. -/
theorem flatten_composeRefinement :
    (B.flatten Q).flatten R = B.flatten (B.composeRefinement Q R) := by
  have ext : ∀ {A C : BlockShape n} (h : A.length = C.length),
      (∀ k, A.size k = C.size (Fin.cast h k)) → A = C := by
    rintro ⟨l, s, hp, hs⟩ ⟨l', s', hp', hs'⟩ h hsize
    dsimp only at h hsize
    subst l'
    have heq : s = s' := funext hsize
    subst s'
    rfl
  exact ext (B.flatten_composeRefinement_length Q R) (B.flatten_composeRefinement_size Q R)

/-- Standard coordinates of a fine block expand through the original outer and
middle blocks, with the middle-rank equality cast in its forward direction. -/
theorem nestedFlatten_index (p : B.RefinementTriple Q R)
    (c : Fin ((R (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)).size p.2.2)) :
    ((B.flatten Q).flatten R).index (B.nestedFlattenBlockEquiv Q R p)
        (Fin.cast (B.nestedFlatten_size Q R p).symm c) =
      B.index p.1 ((Q p.1).index p.2.1
        (Fin.cast (B.flatten_size_flattenBlockEquiv Q ⟨p.1, p.2.1⟩)
          ((R (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)).index p.2.2 c))) := by
  calc
    _ = (B.flatten Q).index (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)
        ((R (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)).index p.2.2 c) :=
      ((B.flatten Q).index_index_eq_flatten R
        ⟨B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩, p.2.2⟩ c).symm
    _ = _ := by
      have h := B.index_index_eq_flatten Q ⟨p.1, p.2.1⟩
        (Fin.cast (B.flatten_size_flattenBlockEquiv Q ⟨p.1, p.2.1⟩)
          ((R (B.flattenBlockEquiv Q ⟨p.1, p.2.1⟩)).index p.2.2 c))
      simpa only [Fin.cast_cast, Fin.cast_eq_self] using h.symm

/-- The exact shape equality transports the standard coordinate embedding using
precisely the proved block-count and fine-rank casts. -/
theorem flatten_composeRefinement_index (k : Fin ((B.flatten Q).flatten R).length)
    (c : Fin (((B.flatten Q).flatten R).size k)) :
    ((B.flatten Q).flatten R).index k c =
      (B.flatten (B.composeRefinement Q R)).index
        (Fin.cast (B.flatten_composeRefinement_length Q R) k)
        (Fin.cast (B.flatten_composeRefinement_size Q R k) c) := by
  have transport : ∀ {A C : BlockShape n} (h : A = C)
      (k : Fin A.length) (c : Fin (A.size k)),
      A.index k c = C.index (Fin.cast (congrArg BlockShape.length h) k)
        (Fin.cast (by cases h; rfl) c) := by
    rintro A C rfl k c
    rfl
  exact transport (B.flatten_composeRefinement Q R) k c

end Langlands.GeneralLinear.BlockShape
