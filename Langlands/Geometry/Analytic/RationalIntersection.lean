import Langlands.Geometry.Analytic.RationalIntersection.Statement
import Langlands.Geometry.Analytic.RationalLocalization
import Mathlib.RingTheory.Ideal.Operations

/-! # Intersections of actual rational localization spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalIntersection

open StrictTateAlgebra PresentedStrictAffinoidAlgebra
open scoped Pointwise

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (P : PresentedStrictAffinoidAlgebra K)
  (m n : ℕ) (g h : P) (f : Fin m → P) (k : Fin n → P)

theorem range_numerators :
    Set.range (numerators K P m n g h f k) =
      insert g (Set.range f) * insert h (Set.range k) := by
  rw [← Fin.range_cons, ← Fin.range_cons]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact Set.mem_mul.mpr ⟨_, Set.mem_range_self _, _, Set.mem_range_self _, rfl⟩
  · rintro ⟨b, ⟨i, rfl⟩, c, ⟨j, rfl⟩, rfl⟩
    exact ⟨finProdFinEquiv (i, j), numerators_pair K P m n g h f k i j⟩

/-- The product tuple generates the unit ideal by multiplication of the
two original unit ideals, including in the zero ring. -/
theorem generatesUnitIdeal
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    RationalLocalization.GeneratesUnitIdeal K P ((m + 1) * (n + 1))
      (g * h) (numerators K P m n g h f k) := by
  have hmem : g * h ∈ Set.range (numerators K P m n g h f k) := by
    refine ⟨finProdFinEquiv (0, 0), ?_⟩
    simp
  change Ideal.span (insert (g * h) (Set.range (numerators K P m n g h f k))) = ⊤
  rw [Set.insert_eq_of_mem hmem, range_numerators, ← Ideal.span_mul_span]
  change Ideal.span (insert g (Set.range f)) * Ideal.span (insert h (Set.range k)) = ⊤
  rw [hf, hk, Ideal.top_mul]

/-- Positivity of a rational denominator follows from its actual unit ideal.
It is not imposed on the point as additional data. -/
theorem denominator_pos (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (x : BanachSpectrum P) (hx : x ∈ RationalLocalization.locus K P m g f) :
    0 < x g := by
  have hne : x g ≠ 0 := by
    intro hg
    have hle : Ideal.span (insert g (Set.range f)) ≤ x.kernel := by
      apply Ideal.span_le.mpr
      intro a ha
      rcases ha with rfl | ⟨i, rfl⟩
      · exact hg
      · exact le_antisymm ((hx i).trans_eq hg) (apply_nonneg x.toMulRingSeminorm _)
    have h1 : x (1 : P) = 0 := hle (by rw [hf]; trivial)
    exact one_ne_zero ((map_one x.toMulRingSeminorm).symm.trans h1)
  exact lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _) hne.symm

/-- The combined inequalities cut out exactly the intersection. -/
theorem locus_eq_inter
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    RationalLocalization.locus K P ((m + 1) * (n + 1))
        (g * h) (numerators K P m n g h f k) =
      RationalLocalization.locus K P m g f ∩ RationalLocalization.locus K P n h k := by
  ext x
  constructor
  · intro hx
    have hpos := denominator_pos K P ((m + 1) * (n + 1)) (g * h)
      (numerators K P m n g h f k) (generatesUnitIdeal K P m n g h f k hf hk) x hx
    rw [map_mul] at hpos
    have hgpos : 0 < x g := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) (apply_nonneg x.toMulRingSeminorm g)
      rw [hz, zero_mul] at hpos
      exact (lt_irrefl 0) hpos
    have hhpos : 0 < x h := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) (apply_nonneg x.toMulRingSeminorm h)
      rw [hz, mul_zero] at hpos
      exact (lt_irrefl 0) hpos
    constructor
    · intro i
      have hi := hx (finProdFinEquiv (i.succ, 0))
      simp only [numerators_pair, Fin.cons_succ, Fin.cons_zero, map_mul] at hi
      exact (mul_le_mul_iff_left₀ hhpos).mp hi
    · intro j
      have hj := hx (finProdFinEquiv (0, j.succ))
      simp only [numerators_pair, Fin.cons_succ, Fin.cons_zero, map_mul] at hj
      exact (mul_le_mul_iff_right₀ hgpos).mp hj
  · rintro ⟨hxf, hxk⟩ a
    have hf' : ∀ i, x ((Fin.cons g f : Fin (m + 1) → P) i) ≤ x g :=
      Fin.cases (le_refl _) (fun i => hxf i)
    have hk' : ∀ j, x ((Fin.cons h k : Fin (n + 1) → P) j) ≤ x h :=
      Fin.cases (le_refl _) (fun j => hxk j)
    change x ((Fin.cons g f : Fin (m + 1) → P) (finProdFinEquiv.symm a).1 *
      (Fin.cons h k : Fin (n + 1) → P) (finProdFinEquiv.symm a).2) ≤ x (g * h)
    rw [map_mul, map_mul]
    exact mul_le_mul (hf' _) (hk' _) (apply_nonneg x.toMulRingSeminorm _)
      (apply_nonneg x.toMulRingSeminorm _)

variable [CompleteSpace K]

theorem range_comap_baseMap
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    Set.range (BanachSpectrum.comap (baseMap K P m n g h f k).toBoundedRingHom) =
      RationalLocalization.locus K P m g f ∩ RationalLocalization.locus K P n h k := by
  exact (RationalLocalization.range_comap_baseMap _ _ _ _ _
    (generatesUnitIdeal K P m n g h f k hf hk)).trans
      (locus_eq_inter K P m n g h f k hf hk)

theorem comap_baseMap_closedEmbedding
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    Topology.IsClosedEmbedding (BanachSpectrum.comap
      (baseMap K P m n g h f k).toBoundedRingHom) :=
  RationalLocalization.comap_baseMap_closedEmbedding _ _ _ _ _
    (generatesUnitIdeal K P m n g h f k hf hk)

theorem coordinate_equation (i : Fin (m + 1)) (j : Fin (n + 1)) :
    baseMap K P m n g h f k (g * h) * fractionCoordinate K P m n g h f k i j =
      baseMap K P m n g h f k
        ((Fin.cons g f : Fin (m + 1) → P) i * (Fin.cons h k : Fin (n + 1) → P) j) := by
  exact (RationalLocalization.coordinate_equation _ _ _ _ _
    (finProdFinEquiv (i, j))).trans (congrArg (baseMap K P m n g h f k)
      (numerators_pair K P m n g h f k i j))

/-- Any finite tuple selected from the new coordinates is power bounded.
This uses the actual bounded quotient map from the Tate algebra. -/
theorem fractionTuple_bounded (r : ℕ)
    (a : Fin r → Fin (m + 1)) (b : Fin r → Fin (n + 1)) :
    HasBoundedMonomials (Fin r) (algebra K P m n g h f k)
      (fun i => fractionCoordinate K P m n g h f k (a i) (b i)) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro i
  exact (hasBoundedMonomials_map_X
    (Fin (algebra K P m n g h f k).arity) K (algebra K P m n g h f k)
    (presentationMap K (algebra K P m n g h f k))).pow_bound _ _
      (Fin.natAdd P.arity (finProdFinEquiv (a i, b i)))

theorem isUnit_denominators
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    IsUnit (baseMap K P m n g h f k g) ∧ IsUnit (baseMap K P m n g h f k h) := by
  have hunit : IsUnit (baseMap K P m n g h f k g * baseMap K P m n g h f k h) := by
    rw [← map_mul]
    exact RationalLocalization.isUnit_baseMap_denominator _ _ _ _ _
      (generatesUnitIdeal K P m n g h f k hf hk)
  exact ⟨isUnit_of_mul_isUnit_left hunit, isUnit_of_mul_isUnit_right hunit⟩

theorem left_coordinate_equation
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) (i : Fin m) :
    baseMap K P m n g h f k g * fractionCoordinate K P m n g h f k i.succ 0 =
      baseMap K P m n g h f k (f i) := by
  apply (isUnit_denominators K P m n g h f k hf hk).2.mul_right_cancel
  calc
    _ = baseMap K P m n g h f k (g * h) *
        fractionCoordinate K P m n g h f k i.succ 0 := by rw [map_mul]; ring
    _ = baseMap K P m n g h f k (f i * h) := by
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        coordinate_equation K P m n g h f k i.succ 0
    _ = _ := map_mul _ _ _

theorem right_coordinate_equation
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) (j : Fin n) :
    baseMap K P m n g h f k h * fractionCoordinate K P m n g h f k 0 j.succ =
      baseMap K P m n g h f k (k j) := by
  apply (isUnit_denominators K P m n g h f k hf hk).1.mul_left_cancel
  calc
    _ = baseMap K P m n g h f k (g * h) *
        fractionCoordinate K P m n g h f k 0 j.succ := by rw [map_mul]; ring
    _ = baseMap K P m n g h f k (g * k j) := by
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        coordinate_equation K P m n g h f k 0 j.succ
    _ = _ := map_mul _ _ _

/-- Bounded restriction from the left rational localization to the intersection. -/
def leftMap
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    BoundedAlgHom K (RationalLocalization.algebra K P m g f) (algebra K P m n g h f k) :=
  RationalLocalization.liftFromBase K P m g f (algebra K P m n g h f k)
    (baseMap K P m n g h f k) (fun i => fractionCoordinate K P m n g h f k i.succ 0)
    (fractionTuple_bounded K P m n g h f k m Fin.succ (fun _ => 0))
    (left_coordinate_equation K P m n g h f k hf hk)

/-- Bounded restriction from the right rational localization to the intersection. -/
def rightMap
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    BoundedAlgHom K (RationalLocalization.algebra K P n h k) (algebra K P m n g h f k) :=
  RationalLocalization.liftFromBase K P n h k (algebra K P m n g h f k)
    (baseMap K P m n g h f k) (fun j => fractionCoordinate K P m n g h f k 0 j.succ)
    (fractionTuple_bounded K P m n g h f k n (fun _ => 0) Fin.succ)
    (right_coordinate_equation K P m n g h f k hf hk)

theorem leftMap_comp_baseMap
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    (leftMap K P m n g h f k hf hk).comp (RationalLocalization.baseMap K P m g f) =
      baseMap K P m n g h f k :=
  RationalLocalization.liftFromBase_comp_baseMap _ _ _ _ _ _ _ _ _ _

theorem rightMap_comp_baseMap
    (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (hk : RationalLocalization.GeneratesUnitIdeal K P n h k) :
    (rightMap K P m n g h f k hf hk).comp (RationalLocalization.baseMap K P n h k) =
      baseMap K P m n g h f k :=
  RationalLocalization.liftFromBase_comp_baseMap _ _ _ _ _ _ _ _ _ _

/-- The product construction identifies the intersection and admits bounded
restriction maps from both rational localization algebras. -/
theorem intersection : IntersectionStatement.{u} := by
  intro K _ _ _ P m n g h f k hf hk
  exact ⟨generatesUnitIdeal K P m n g h f k hf hk,
    locus_eq_inter K P m n g h f k hf hk,
    range_comap_baseMap K P m n g h f k hf hk,
    comap_baseMap_closedEmbedding K P m n g h f k hf hk,
    leftMap K P m n g h f k hf hk, rightMap K P m n g h f k hf hk,
    leftMap_comp_baseMap K P m n g h f k hf hk,
    rightMap_comp_baseMap K P m n g h f k hf hk⟩

end Langlands.Analytic.RationalIntersection
