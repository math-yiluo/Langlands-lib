import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual products of natural vector-coordinate blocks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- The all-test subgroup with coordinates outside `I` equal to zero. -/
def vectorCoordinateSubgroup (he : IsNaturalVectorCoordinates e) (I : Set (Fin d)) :
    SubgroupFunctor V where
  carrier T :=
    { carrier := {v | ∀ a, a ∉ I → (e T v).toAdd a = 0}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy a ha
        simp only [map_mul, toAdd_mul, Pi.add_apply, hx a ha, hy a ha,
          add_zero]
      inv_mem' := by
        intro x hx a ha
        simp only [map_inv, toAdd_inv, Pi.neg_apply, hx a ha, neg_zero] }
  comp_mem := by
    intro T W f v hv a ha
    rw [he T W f]
    exact (congrArg f.left.appTop (hv a ha)).trans (map_zero _)

/-- Set the coordinates outside `I` to zero on every test scheme. -/
def vectorCoordinateProjectionPoints (I : Set (Fin d))
    (T : Over (Spec (CommRingCat.of k))) : (T ⟶ V.X) →* (T ⟶ V.X) := by
  classical
  refine
    { toFun := fun v => (e T).symm
        (Multiplicative.ofAdd (fun a => if a ∈ I then (e T v).toAdd a else 0))
      map_one' := ?_
      map_mul' := ?_ }
  · apply (e T).injective
    simp
    rfl
  · intro x y
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext a
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_mul,
      toAdd_ofAdd, Pi.add_apply]
    split_ifs <;> simp

open Classical in
@[simp]
theorem vectorCoordinateProjectionPoints_coord (I : Set (Fin d))
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) (a : Fin d) :
    (e T (vectorCoordinateProjectionPoints e I T v)).toAdd a =
      if a ∈ I then (e T v).toAdd a else 0 := by
  classical
  exact congrArg (fun z => z.toAdd a) ((e T).apply_symm_apply _)

variable {e}

/-- Coordinate projection is natural on arbitrary test schemes. -/
theorem IsNaturalVectorCoordinates.vectorCoordinateProjection_natural
    (he : IsNaturalVectorCoordinates e) (I : Set (Fin d))
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T) (v : T ⟶ V.X) :
    vectorCoordinateProjectionPoints e I W (f ≫ v) =
      f ≫ vectorCoordinateProjectionPoints e I T v := by
  classical
  apply (e W).injective
  apply Multiplicative.toAdd.injective
  funext a
  rw [vectorCoordinateProjectionPoints_coord, he T W f,
    he T W f]
  dsimp only
  rw [vectorCoordinateProjectionPoints_coord]
  split_ifs <;> simp

variable (e)

/-- The actual group-scheme endomorphism projecting onto a coordinate block. -/
def vectorCoordinateProjection (he : IsNaturalVectorCoordinates e) (I : Set (Fin d)) :
    V ⟶ V :=
  homOfPoints (vectorCoordinateProjectionPoints e I)
    (he.vectorCoordinateProjection_natural I)

@[simp]
theorem comp_vectorCoordinateProjection (he : IsNaturalVectorCoordinates e)
    (I : Set (Fin d)) (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) :
    v ≫ (vectorCoordinateProjection e he I).hom.hom =
      vectorCoordinateProjectionPoints e I T v :=
  comp_homOfPoints _ _ T v

/-- Its actual range is precisely the coordinate subgroup on every test. -/
theorem range_vectorCoordinateProjection (he : IsNaturalVectorCoordinates e)
    (I : Set (Fin d)) :
    SubgroupFunctor.range (vectorCoordinateProjection e he I) =
      vectorCoordinateSubgroup e he I := by
  classical
  ext T v
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩ a ha
    simp only [comp_vectorCoordinateProjection, vectorCoordinateProjectionPoints_coord,
      ite_eq_right ha]
  · intro hv
    refine ⟨v, ?_⟩
    rw [comp_vectorCoordinateProjection]
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext a
    rw [vectorCoordinateProjectionPoints_coord]
    split_ifs with ha
    · rfl
    · exact (hv a ha).symm

private def vectorCoordinateEval (T : Over (Spec (CommRingCat.of k))) (a : Fin d) :
    (T ⟶ V.X) →* Multiplicative Γ(T.left, ⊤) where
  toFun v := Multiplicative.ofAdd ((e T v).toAdd a)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul, Pi.add_apply]
    rfl

private theorem vectorCoordinateEval_orderedPoints {n : ℕ}
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))} (j : ∀ r, H r ⟶ V)
    {T : Over (Spec (CommRingCat.of k))} (x : ∀ r, T ⟶ (H r).X) (a : Fin d) :
    vectorCoordinateEval e T a (orderedPoints j x) =
      ∏ r, vectorCoordinateEval e T a (x r ≫ (j r).hom.hom) := by
  simp only [orderedPoints, map_list_prod, List.map_ofFn, Function.comp_def,
    Fin.prod_ofFn]

/-- A finite partition of the vector coordinates gives a scheme isomorphism
from any actual representatives of its coordinate subgroups, by the original
ordered multiplication. The empty partition is included. -/
theorem isIso_orderedMultiplication_vectorCoordinates
    (he : IsNaturalVectorCoordinates e) {n : ℕ} (I : Fin n → Set (Fin d))
    (hI : ∀ a, ∃! r, a ∈ I r)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))} (j : ∀ r, H r ⟶ V)
    (hj : ∀ r, (vectorCoordinateSubgroup e he (I r)).IsRepresentedBy (j r)) :
    IsIso (orderedMultiplication j) := by
  classical
  have coord {T : Over (Spec (CommRingCat.of k))}
      (x : ∀ r, T ⟶ (H r).X) (r : Fin n) (a : Fin d) (ha : a ∈ I r) :
      vectorCoordinateEval e T a (orderedPoints j x) =
        vectorCoordinateEval e T a (x r ≫ (j r).hom.hom) := by
    rw [vectorCoordinateEval_orderedPoints]
    apply Finset.prod_eq_single r
    · intro s _ hsr
      have has : a ∉ I s := fun hs => hsr ((hI a).unique hs ha)
      have hx := ((hj s).pointsEquiv T (x s)).property a has
      exact congrArg Multiplicative.ofAdd hx
    · simp
  apply (isIso_orderedMultiplication_iff j).2
  intro T
  constructor
  · intro x y hxy
    funext r
    apply (hj r).1.right_cancellation
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext a
    by_cases ha : a ∈ I r
    · have h := congrArg (vectorCoordinateEval e T a) hxy
      rw [coord x r a ha, coord y r a ha] at h
      exact congrArg Multiplicative.toAdd h
    · exact (((hj r).pointsEquiv T (x r)).property a ha).trans
        (((hj r).pointsEquiv T (y r)).property a ha).symm
  · intro v
    let x : ∀ r, T ⟶ (H r).X := fun r =>
      ((hj r).pointsEquiv T).symm
        ⟨vectorCoordinateProjectionPoints e (I r) T v, by
          intro a ha
          simp only [vectorCoordinateProjectionPoints_coord, ite_eq_right ha]⟩
    refine ⟨x, ?_⟩
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext a
    obtain ⟨r, ha, _⟩ := hI a
    have hx : x r ≫ (j r).hom.hom =
        vectorCoordinateProjectionPoints e (I r) T v :=
      (hj r).pointsEquiv_symm_comp _
    have h := coord x r a ha
    rw [hx] at h
    have h' : (e T (orderedPoints j x)).toAdd a =
        (e T (vectorCoordinateProjectionPoints e (I r) T v)).toAdd a :=
      congrArg Multiplicative.toAdd h
    simpa only [vectorCoordinateProjectionPoints_coord, ite_eq_left ha] using h'

end Langlands.GroupScheme.RelativeRoot
