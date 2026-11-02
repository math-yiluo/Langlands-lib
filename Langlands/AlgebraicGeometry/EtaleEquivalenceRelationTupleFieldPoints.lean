import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleFiltration
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossQuotient

/-! # Field points of distinct tuples and maximal-tuple matching -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

/-- For a field-valued tuple, avoiding all equality loci is equivalent to
injectivity of its coordinate morphisms. -/
theorem range_subset_tupleDistinctOpen_iff_of_field (n : ℕ) (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ E.tupleScheme n) :
    Set.range f ⊆ E.tupleDistinctOpen n ↔
      Function.Injective (fun i => f ≫ E.tupleProjection n i) := by
  constructor
  · intro hf
    let g := IsOpenImmersion.lift (E.tupleDistinctOpen n).ι f
      (by simpa using hf)
    have hg : g ≫ (E.tupleDistinctOpen n).ι = f :=
      IsOpenImmersion.lift_fac _ _ _
    have hi := E.tupleDistinct_coordinates_injective n g
    simpa only [tupleDistinctProjection, ← Category.assoc, hg] using hi
  · intro hi
    rintro _ ⟨x, rfl⟩
    apply (E.mem_tupleDistinctOpen n (f x)).mpr
    intro i j hij heq
    have hr : Set.range f ⊆ E.tupleEqualOpen n i j := by
      rintro _ ⟨y, rfl⟩
      change f y ∈ E.tupleEqualOpen n i j
      have hy : y = x := Subsingleton.elim _ _
      subst y
      exact heq
    exact hij (hi ((E.range_subset_tupleEqualOpen_iff n i j f).mp hr))

/-- Realize a pairwise related injective family of field-valued coordinates
as a point of the distinct-tuple scheme. -/
def tupleDistinctFieldLift (n : ℕ) (K : Type u) [Field K]
    (a : Fin (n + 1) → (Spec (.of K) ⟶ E.U))
    (h : ∀ i j, ∃ r : Spec (.of K) ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j)
    (ha : Function.Injective a) : Spec (.of K) ⟶ E.tupleDistinctScheme n :=
  IsOpenImmersion.lift (E.tupleDistinctOpen n).ι (E.tupleLift n a h)
    (by
      rw [Scheme.Opens.range_ι]
      apply (E.range_subset_tupleDistinctOpen_iff_of_field n K _).mpr
      simpa only [E.tupleLift_projection] using ha)

@[reassoc (attr := simp)]
theorem tupleDistinctFieldLift_projection (n : ℕ) (K : Type u) [Field K]
    (a : Fin (n + 1) → (Spec (.of K) ⟶ E.U))
    (h : ∀ i j, ∃ r : Spec (.of K) ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j)
    (ha : Function.Injective a) (i : Fin (n + 1)) :
    E.tupleDistinctFieldLift n K a h ha ≫ E.tupleDistinctProjection n i = a i := by
  simp only [tupleDistinctFieldLift, tupleDistinctProjection, ← Category.assoc,
    IsOpenImmersion.lift_fac, E.tupleLift_projection]

/-- Outside the next tuple threshold, every related field-valued coordinate
already occurs in a given injective family of `n + 1` coordinates. -/
theorem tupleField_coordinates_exhaust (n : ℕ) (K : Type u) [Field K]
    (a : Fin (n + 1) → (Spec (.of K) ⟶ E.U))
    (h : ∀ i j, ∃ r : Spec (.of K) ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j)
    (ha : Function.Injective a) (b : Spec (.of K) ⟶ E.U)
    (hb : ∀ i, ∃ r : Spec (.of K) ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = b)
    (hx : (a 0) default ∉ E.tupleThresholdOpen (n + 1)) :
    ∃ i, a i = b := by
  classical
  by_contra hnot
  have hab : b ∉ Set.range a := by
    simpa only [Set.mem_range] using hnot
  have hinj : Function.Injective (Fin.snoc a b) :=
    Fin.snoc_injective_iff.mpr ⟨ha, hab⟩
  let c : Fin (n + 2) → (Spec (.of K) ⟶ E.U) := Fin.snoc a b
  have hrel : ∀ i j : Fin (n + 2), ∃ r : Spec (.of K) ⟶ E.R,
      r ≫ E.t = c i ∧ r ≫ E.s = c j := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [c] using E.refl (Spec (.of K)) b
      · obtain ⟨r, hrt, hrs⟩ := hb j
        obtain ⟨r', hr't, hr's⟩ := E.symm (Spec (.of K)) r
        exact ⟨r', by simpa [c] using hr't.trans hrs, by simpa [c] using hr's.trans hrt⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [c] using hb i
      · simpa [c] using h i j
  let f := E.tupleDistinctFieldLift (n + 1) K c hrel hinj
  have hmem : (a 0) default ∈ E.tupleImageOpen (n + 1) := by
    refine ⟨f default, ?_⟩
    change (f ≫ E.tupleDistinctProjection (n + 1) 0) default = (a 0) default
    dsimp only [f]
    rw [E.tupleDistinctFieldLift_projection]
    rfl
  exact hx (E.le_pointSaturationOpen _ hmem)

/-- A global matching of each coordinate in the second distinct tuple with
one in the first gives a single coordinate permutation. -/
theorem tupleDistinct_exists_permutation (n : ℕ) {T : Scheme.{u}} [Nonempty T]
    (a b : T ⟶ E.tupleDistinctScheme n)
    (h : ∀ j, ∃ i, a ≫ E.tupleDistinctProjection n i =
      b ≫ E.tupleDistinctProjection n j) :
    ∃ g : Equiv.Perm (Fin (n + 1)), a ≫ (E.tupleDistinctReindexIso g).hom = b := by
  classical
  let g : Fin (n + 1) → Fin (n + 1) := fun j => (h j).choose
  have hg : ∀ j, a ≫ E.tupleDistinctProjection n (g j) =
      b ≫ E.tupleDistinctProjection n j := fun j => (h j).choose_spec
  have hginj : Function.Injective g := by
    intro i j hij
    apply E.tupleDistinct_coordinates_injective n b
    exact (hg i).symm.trans ((congrArg (fun k => a ≫ E.tupleDistinctProjection n k) hij).trans
      (hg j))
  let e := Equiv.ofBijective g ⟨hginj, Finite.surjective_of_injective hginj⟩
  refine ⟨e, ?_⟩
  apply E.tupleDistinct_hom_ext n
  intro i
  simpa [e] using hg i

section Affine

variable [IsAffine E.U] [IsAffine E.R]

theorem tupleSymmetricMap_eq_of_coordinate_matching (n : ℕ)
    {T : Scheme.{u}} [Nonempty T] (a b : T ⟶ E.tupleDistinctScheme n)
    (h : ∀ j, ∃ i, a ≫ E.tupleDistinctProjection n i =
      b ≫ E.tupleDistinctProjection n j) :
    a ≫ E.tupleSymmetricMap n = b ≫ E.tupleSymmetricMap n := by
  obtain ⟨g, hg⟩ := E.tupleDistinct_exists_permutation n a b h
  rw [← hg]
  simp

/-- Ordered cross arrows outside the next threshold have equal unordered
endpoints on every field-valued point. -/
theorem tupleCross_fieldPoint_symmetric_eq_of_not_threshold
    (n : ℕ) (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ E.tupleCrossScheme n n)
    (hx : (f ≫ E.tupleCrossLeft n n ≫ E.tupleDistinctProjection n 0) default ∉
      E.tupleThresholdOpen (n + 1)) :
    f ≫ E.tupleCrossLeft n n ≫ E.tupleSymmetricMap n =
      f ≫ E.tupleCrossRight n n ≫ E.tupleSymmetricMap n := by
  let a := fun i => f ≫ E.tupleCrossLeft n n ≫ E.tupleDistinctProjection n i
  have ha : Function.Injective a := by
    simpa [a, ← Category.assoc] using
      E.tupleDistinct_coordinates_injective n (f ≫ E.tupleCrossLeft n n)
  have hrel : ∀ i j, ∃ r : Spec (.of K) ⟶ E.R,
      r ≫ E.t = a i ∧ r ≫ E.s = a j := by
    intro i j
    refine ⟨f ≫ E.tupleCrossLeft n n ≫ (E.tupleDistinctOpen n).ι ≫
      E.tupleRelation n i j, ?_, ?_⟩
    · simp [a, tupleDistinctProjection]
    · simp [a, tupleDistinctProjection]
  apply E.tupleSymmetricMap_eq_of_coordinate_matching n
    (f ≫ E.tupleCrossLeft n n) (f ≫ E.tupleCrossRight n n)
  intro j
  have hb : ∀ i, ∃ r : Spec (.of K) ⟶ E.R,
      r ≫ E.t = a i ∧
      r ≫ E.s = f ≫ E.tupleCrossRight n n ≫ E.tupleDistinctProjection n j := by
    intro i
    obtain ⟨r, hrt, hrs⟩ := E.tupleCrossCoordinates_related n n i j
    exact ⟨f ≫ r, by simpa [a] using congrArg (f ≫ ·) hrt,
      by simpa using congrArg (f ≫ ·) hrs⟩
  simpa [a, Category.assoc] using
    E.tupleField_coordinates_exhaust n K a hrel ha
      (f ≫ E.tupleCrossRight n n ≫ E.tupleDistinctProjection n j) hb hx

end Affine

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
