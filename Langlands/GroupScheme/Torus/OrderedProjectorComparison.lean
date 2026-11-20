import Langlands.GroupScheme.Torus.OrderedProjectorRepresentation

/-! # Comparing ordered projector families by their weight coefficients -/

noncomputable section

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.OrderedProjectorScheme

variable {J K n : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype n] [DecidableEq n]

/-- Relabel the projectors by an equivalence of label sets. -/
def Family.relabel {A : Type u} [CommRing A] (Q : Family K n A) (e : J ≃ K) : Family J n A where
  matrix i := Q.matrix (e i)
  mul_eq i j := by simp only [Q.mul_eq, e.injective.eq_iff]
  sum_eq := (Equiv.sum_comp e Q.matrix).trans Q.sum_eq
  entryIdeal_eq_top i := Q.entryIdeal_eq_top (e i)

/-- Relabelling and taking the corresponding family of unit scalars gives the same matrix. -/
theorem weightedUnit_relabel {A : Type u} [CommRing A] (Q : Family K n A) (e : J ≃ K)
    (c : K → Aˣ) : weightedUnit (Q.relabel e) (c ∘ e) = weightedUnit Q c := by
  apply Units.ext
  change (∑ i : J, (c (e i) : A) • Q.matrix (e i)) = ∑ i : K, (c i : A) • Q.matrix i
  exact Equiv.sum_comp e (fun i => (c i : A) • Q.matrix i)

section Coefficients

variable {A : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  (w : J → Λ) (P : Family J n A)

/-- The entry of the universal matrix is the sum of its labelled monomials. -/
theorem characterMatrix_entry (a b : n) :
    characterMatrix w P a b = ∑ i, AddMonoidAlgebra.single (w i) (P.matrix i a b) := by
  change (weightedMatrix (P.map (algebraMap A (AddMonoidAlgebra A Λ)))
    (fun i => (Diagonalizable.monomialUnits A Λ (.ofAdd (w i)) : AddMonoidAlgebra A Λ))) a b = _
  simp only [weightedMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  change AddMonoidAlgebra.single (w i) 1 * AddMonoidAlgebra.single 0 (P.matrix i a b) = _
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

/-- A weight that occurs at a unique label has the corresponding projector as coefficient. -/
theorem characterMatrix_coeff_weight (hw : Function.Injective w) (i : J) (a b : n) :
    (characterMatrix w P a b).coeff (w i) = P.matrix i a b := by
  classical
  rw [characterMatrix_entry, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hjw : w j ≠ w i := fun h => hj (hw h)
    simp [hjw]
  · simp

/-- A weight absent from the labels has zero coefficient. -/
theorem characterMatrix_coeff_of_notMem {m : Λ} (hm : m ∉ Set.range w) (a b : n) :
    (characterMatrix w P a b).coeff m = 0 := by
  classical
  rw [characterMatrix_entry, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : w i ≠ m := fun h => hm ⟨i, h⟩
  simp [hi]

/-- With a nonzero base and positive projector ranks, the labelled weights are exactly
those with nonzero matrix coefficient. -/
theorem mem_weights_iff [Nontrivial A] (hw : Function.Injective w) (m : Λ) :
    m ∈ Set.range w ↔ ∃ a b, (characterMatrix w P a b).coeff m ≠ 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    have hne : P.matrix i ≠ 0 := by
      intro h
      have hi := P.entryIdeal_eq_top i
      rw [(entryIdeal_eq_bot _).mpr h] at hi
      exact bot_ne_top hi
    by_contra! h
    apply hne
    ext a b
    exact (characterMatrix_coeff_weight w P hw i a b).symm.trans (h a b)
  · rintro ⟨a, b, h⟩
    by_contra hm
    exact h (characterMatrix_coeff_of_notMem w P hm a b)

/-- Equality of two universal matrices with distinct weights gives a matching
of labels and equality of the corresponding projectors. -/
theorem exists_relabel_of_characterMatrix_eq [Nontrivial A]
    (v : K → Λ) (Q : Family K n A) (hw : Function.Injective w) (hv : Function.Injective v)
    (h : characterMatrix w P = characterMatrix v Q) :
    ∃ e : J ≃ K, (∀ i, w i = v (e i)) ∧ P = Q.relabel e := by
  have hr : Set.range w = Set.range v := by
    ext m
    rw [mem_weights_iff w P hw, mem_weights_iff v Q hv, h]
  let e := (Equiv.ofInjective w hw).trans
    ((Equiv.subtypeEquivRight (Set.ext_iff.mp hr)).trans (Equiv.ofInjective v hv).symm)
  have he : ∀ i, w i = v (e i) := by
    intro i
    let m : Set.range v :=
      Equiv.subtypeEquivRight (Set.ext_iff.mp hr) (Equiv.ofInjective w hw i)
    change (m : Λ) = v ((Equiv.ofInjective v hv).symm m)
    exact (Equiv.apply_ofInjective_symm hv m).symm
  refine ⟨e, he, Family.ext (funext fun i => ?_)⟩
  ext a b
  change P.matrix i a b = Q.matrix (e i) a b
  rw [← characterMatrix_coeff_weight w P hw, ← characterMatrix_coeff_weight v Q hv, h, he]

end Coefficients

section WeightEquivalence

variable {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
    (w : J → Λ) (v : K → Λ')

/-- A matching of two weight sets through a character lattice isomorphism. -/
@[ext]
structure WeightEquivalence where
  lattice : Λ' ≃+ Λ
  labels : J ≃ K
  weight_eq : ∀ i, w i = lattice (v (labels i))

omit [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] in
/-- The label permutation determines the lattice isomorphism because the weights generate. -/
theorem WeightEquivalence.labels_injective (hv : AddSubgroup.closure (Set.range v) = ⊤) :
    Function.Injective (WeightEquivalence.labels : WeightEquivalence w v → J ≃ K) := by
  intro p q h
  have hmap : p.lattice.toAddMonoidHom = q.lattice.toAddMonoidHom := by
    apply AddMonoidHom.eq_of_eqOn_dense hv
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := p.labels.surjective i
    change p.lattice (v (p.labels j)) = q.lattice (v (p.labels j))
    rw [← p.weight_eq, h, ← q.weight_eq]
  refine WeightEquivalence.ext ?_ h
  ext m
  exact DFunLike.congr_fun hmap m

omit [DecidableEq J] [Fintype K] [DecidableEq K] in
/-- There are only finitely many matchings of two generating ordered weight sets. -/
theorem WeightEquivalence.finite (hv : AddSubgroup.closure (Set.range v) = ⊤) :
    Finite (WeightEquivalence w v) :=
  Finite.of_injective _ (WeightEquivalence.labels_injective w v hv)

end WeightEquivalence

end Langlands.GroupScheme.OrderedProjectorScheme
