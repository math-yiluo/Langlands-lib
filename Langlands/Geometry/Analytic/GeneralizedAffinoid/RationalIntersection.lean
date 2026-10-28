import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectrum
import Mathlib.RingTheory.Ideal.Operations

/-! # Product presentations for positive-polyradius rational intersections -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection

open GeneralizedTateAlgebra
open scoped Pointwise

/-- Give the products of two denominator-extended tuples their product radii.
The new denominator entries have radius one. -/
def productRadii {m n : ℕ} (s : PositivePolyradius (Fin m))
    (t : PositivePolyradius (Fin n)) : PositivePolyradius (Fin ((m + 1) * (n + 1))) where
  radius a := (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) (finProdFinEquiv.symm a).2
  positive a := mul_pos
    (Fin.cases (by simp) (fun i => by simpa using s.positive i) (finProdFinEquiv.symm a).1)
    (Fin.cases (by simp) (fun j => by simpa using t.positive j) (finProdFinEquiv.symm a).2)

@[simp] theorem productRadii_pair {m n : ℕ} (s : PositivePolyradius (Fin m))
    (t : PositivePolyradius (Fin n)) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productRadii s t (finProdFinEquiv (i, j)) =
      (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) i *
        (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) j := by
  change (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ)
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 *
    (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ)
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m n : ℕ}
  (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
  (g h : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (k : Fin n → GeneralizedTateAlgebra A.polyradius K)

/-- All products of the denominator-extended numerator tuples. -/
def numerators : Fin ((m + 1) * (n + 1)) → GeneralizedTateAlgebra A.polyradius K := fun a =>
  (Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K)
      (finProdFinEquiv.symm a).1 *
    (Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K)
      (finProdFinEquiv.symm a).2

@[simp] theorem numerators_pair (i : Fin (m + 1)) (j : Fin (n + 1)) :
    numerators K A g h f k (finProdFinEquiv (i, j)) =
      (Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K) i *
        (Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K) j := by
  simp [numerators]

/-- The actual closed rational quotient at the product denominator and radii. -/
abbrev Algebra : PresentedAffinoidAlgebra K :=
  algebra K A (productRadii s t) (g * h) (numerators K A g h f k)

/-- The structural bounded map from the original coefficient algebra. -/
def base : BoundedAlgHom K A (Algebra K A s t g h f k) :=
  baseMap K A (productRadii s t) (g * h) (numerators K A g h f k)

/-- The actual quotient coordinate indexed by a pair of extended indices. -/
def fractionCoordinate (i : Fin (m + 1)) (j : Fin (n + 1)) : Algebra K A s t g h f k :=
  fraction K A (productRadii s t) (g * h) (numerators K A g h f k)
    (finProdFinEquiv (i, j))

theorem norm_base_le (a : A) : ‖base K A s t g h f k a‖ ≤ ‖a‖ :=
  norm_baseMap_le K A (productRadii s t) (g * h) (numerators K A g h f k) a

/-- The products generate the product of the two original generated ideals. -/
theorem range_mapped_numerators :
    Set.range (fun a => presentationMap K A (numerators K A g h f k a)) =
      insert (presentationMap K A g) (Set.range fun i => presentationMap K A (f i)) *
        insert (presentationMap K A h) (Set.range fun j => presentationMap K A (k j)) := by
  have hfg (i : Fin (m + 1)) : presentationMap K A ((Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K) i) =
      (Fin.cons (presentationMap K A g) (fun i => presentationMap K A (f i)) : Fin (m + 1) → A) i := by
    induction i using Fin.cases <;> simp
  have hkh (j : Fin (n + 1)) : presentationMap K A ((Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K) j) =
      (Fin.cons (presentationMap K A h) (fun j => presentationMap K A (k j)) : Fin (n + 1) → A) j := by
    induction j using Fin.cases <;> simp
  rw [← Fin.range_cons, ← Fin.range_cons]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    refine Set.mem_mul.mpr ⟨_, Set.mem_range_self (finProdFinEquiv.symm b).1,
      _, Set.mem_range_self (finProdFinEquiv.symm b).2, ?_⟩
    simp only [numerators, map_mul]
    rw [hfg, hkh]
  · rintro ⟨b, ⟨i, rfl⟩, c, ⟨j, rfl⟩, rfl⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simp only [numerators_pair, map_mul]
    rw [hfg, hkh]

/-- Including all mixed numerator products preserves unit generation. -/
theorem generatesUnitIdeal (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    GeneratesUnitIdeal K A (g * h) (numerators K A g h f k) := by
  have hmem : presentationMap K A (g * h) ∈
      Set.range (fun a => presentationMap K A (numerators K A g h f k a)) := by
    refine ⟨finProdFinEquiv (0, 0), ?_⟩
    simp
  change Ideal.span (insert (presentationMap K A (g * h))
    (Set.range fun a => presentationMap K A (numerators K A g h f k a))) = ⊤
  rw [Set.insert_eq_of_mem hmem, range_mapped_numerators, ← Ideal.span_mul_span]
  change Ideal.span (insert (presentationMap K A g) (Set.range fun i => presentationMap K A (f i))) *
    Ideal.span (insert (presentationMap K A h) (Set.range fun j => presentationMap K A (k j))) = ⊤
  rw [hf, hk, Ideal.top_mul]

/-- The product-radius inequalities cut out exactly the original intersection. -/
theorem locus_eq_inter (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    locus K A (productRadii s t) (g * h) (numerators K A g h f k) =
      locus K A s g f ∩ locus K A t h k := by
  ext x
  constructor
  · intro hx
    have hpos : 0 < x (presentationMap K A (g * h)) :=
      lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
        (denominator_ne_zero K A (productRadii s t) (g * h) (numerators K A g h f k)
          (generatesUnitIdeal K A g h f k hf hk) x hx).symm
    rw [map_mul, map_mul] at hpos
    have hgpos : 0 < x (presentationMap K A g) := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) (apply_nonneg x.toMulRingSeminorm _)
      rw [hz, zero_mul] at hpos
      exact (lt_irrefl 0) hpos
    have hhpos : 0 < x (presentationMap K A h) := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) (apply_nonneg x.toMulRingSeminorm _)
      rw [hz, mul_zero] at hpos
      exact (lt_irrefl 0) hpos
    constructor
    · intro i
      have hi := hx (finProdFinEquiv (i.succ, 0))
      simp only [numerators_pair, productRadii_pair, Fin.cons_succ, Fin.cons_zero,
        map_mul, mul_one] at hi
      exact (mul_le_mul_iff_left₀ hhpos).mp (by simpa only [mul_assoc] using hi)
    · intro j
      have hj := hx (finProdFinEquiv (0, j.succ))
      simp only [numerators_pair, productRadii_pair, Fin.cons_succ, Fin.cons_zero,
        map_mul, one_mul] at hj
      rw [mul_left_comm (t j)] at hj
      exact (mul_le_mul_iff_right₀ hgpos).mp hj
  · rintro ⟨hxf, hxk⟩ a
    have hf' : ∀ i, x (presentationMap K A ((Fin.cons g f : Fin (m + 1) → _) i)) ≤
        (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) i * x (presentationMap K A g) :=
      Fin.cases (by simp) (fun i => hxf i)
    have hk' : ∀ j, x (presentationMap K A ((Fin.cons h k : Fin (n + 1) → _) j)) ≤
        (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) j * x (presentationMap K A h) :=
      Fin.cases (by simp) (fun j => hxk j)
    change x (presentationMap K A ((Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K) (finProdFinEquiv.symm a).1 *
      (Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K) (finProdFinEquiv.symm a).2)) ≤
        ((Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) (finProdFinEquiv.symm a).1 *
          (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) (finProdFinEquiv.symm a).2) *
            x (presentationMap K A (g * h))
    rw [map_mul, map_mul, map_mul, map_mul]
    calc
      _ ≤ ((Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) (finProdFinEquiv.symm a).1 *
          x (presentationMap K A g)) *
        ((Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) (finProdFinEquiv.symm a).2 *
          x (presentationMap K A h)) :=
        mul_le_mul (hf' _) (hk' _) (apply_nonneg x.toMulRingSeminorm _)
          ((apply_nonneg x.toMulRingSeminorm _).trans (hf' _))
      _ = _ := by ring

/-- Each product coordinate satisfies the actual quotient equation. -/
theorem coordinate_equation (i : Fin (m + 1)) (j : Fin (n + 1)) :
    base K A s t g h f k (presentationMap K A (g * h)) *
        fractionCoordinate K A s t g h f k i j =
      base K A s t g h f k (presentationMap K A
        ((Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K) i *
          (Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K) j)) := by
  have hq := fraction_equation K A (productRadii s t) (g * h) (numerators K A g h f k)
    (finProdFinEquiv (i, j))
  rw [numerators_pair] at hq
  exact hq

theorem norm_fractionCoordinate_le (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ‖fractionCoordinate K A s t g h f k i j‖ ≤
      (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) i *
        (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) j := by
  simpa only [fractionCoordinate, productRadii_pair] using
    norm_fraction_le K A (productRadii s t) (g * h) (numerators K A g h f k)
      (finProdFinEquiv (i, j))

/-- The left fraction is the product coordinate with the right denominator. -/
def leftCoordinate (i : Fin m) : Algebra K A s t g h f k :=
  fractionCoordinate K A s t g h f k i.succ 0

/-- The right fraction is the product coordinate with the left denominator. -/
def rightCoordinate (j : Fin n) : Algebra K A s t g h f k :=
  fractionCoordinate K A s t g h f k 0 j.succ

theorem norm_leftCoordinate_le (i : Fin m) : ‖leftCoordinate K A s t g h f k i‖ ≤ s i := by
  simpa only [leftCoordinate, Fin.cons_succ, Fin.cons_zero, mul_one] using
    norm_fractionCoordinate_le K A s t g h f k i.succ 0

theorem norm_rightCoordinate_le (j : Fin n) : ‖rightCoordinate K A s t g h f k j‖ ≤ t j := by
  simpa only [rightCoordinate, Fin.cons_succ, Fin.cons_zero, one_mul] using
    norm_fractionCoordinate_le K A s t g h f k 0 j.succ

/-- Unit generation makes both original denominators units in the product quotient. -/
theorem isUnit_denominators (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    IsUnit (base K A s t g h f k (presentationMap K A g)) ∧
      IsUnit (base K A s t g h f k (presentationMap K A h)) := by
  have hunit : IsUnit (base K A s t g h f k (presentationMap K A g) *
      base K A s t g h f k (presentationMap K A h)) := by
    rw [← map_mul, ← map_mul]
    exact isUnit_baseMap_denominator K A (productRadii s t) (g * h) (numerators K A g h f k)
      (generatesUnitIdeal K A g h f k hf hk)
  exact ⟨isUnit_of_mul_isUnit_left hunit, isUnit_of_mul_isUnit_right hunit⟩

/-- Cancel the right unit denominator to recover the left rational equation. -/
theorem leftCoordinate_equation
    (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) (i : Fin m) :
    base K A s t g h f k (presentationMap K A g) * leftCoordinate K A s t g h f k i =
      base K A s t g h f k (presentationMap K A (f i)) := by
  apply (isUnit_denominators K A s t g h f k hf hk).2.mul_right_cancel
  calc
    _ = base K A s t g h f k (presentationMap K A (g * h)) *
        fractionCoordinate K A s t g h f k i.succ 0 := by
      simp only [map_mul, leftCoordinate]
      ring
    _ = base K A s t g h f k (presentationMap K A (f i * h)) := by
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        coordinate_equation K A s t g h f k i.succ 0
    _ = _ := by rw [map_mul, map_mul]

/-- Cancel the left unit denominator to recover the right rational equation. -/
theorem rightCoordinate_equation
    (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) (j : Fin n) :
    base K A s t g h f k (presentationMap K A h) * rightCoordinate K A s t g h f k j =
      base K A s t g h f k (presentationMap K A (k j)) := by
  apply (isUnit_denominators K A s t g h f k hf hk).1.mul_left_cancel
  calc
    _ = base K A s t g h f k (presentationMap K A (g * h)) *
        fractionCoordinate K A s t g h f k 0 j.succ := by
      simp only [map_mul, rightCoordinate]
      ring
    _ = base K A s t g h f k (presentationMap K A (g * k j)) := by
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        coordinate_equation K A s t g h f k 0 j.succ
    _ = _ := by rw [map_mul, map_mul]

private theorem leftCoordinate_monomial (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A s t g h f k)
      (leftCoordinate K A s t g h f k) d‖ ≤ s.weight d :=
  monomialValue_norm_le_weight s (Algebra K A s t g h f k)
    (PresentedAffinoidAlgebra.norm_one_le K (Algebra K A s t g h f k))
    (leftCoordinate K A s t g h f k) (norm_leftCoordinate_le K A s t g h f k) d

private theorem rightCoordinate_monomial (d : Fin n →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A s t g h f k)
      (rightCoordinate K A s t g h f k) d‖ ≤ t.weight d :=
  monomialValue_norm_le_weight t (Algebra K A s t g h f k)
    (PresentedAffinoidAlgebra.norm_one_le K (Algebra K A s t g h f k))
    (rightCoordinate K A s t g h f k) (norm_rightCoordinate_le K A s t g h f k) d

/-- The structural spectrum map is actual seminorm precomposition. -/
def baseSpectrumMap : C(BanachSpectrum (Algebra K A s t g h f k), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (base K A s t g h f k).toBoundedRingHom

theorem range_baseSpectrumMap (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    Set.range (baseSpectrumMap K A s t g h f k) = locus K A s g f ∩ locus K A t h k :=
  (range_spectrumMap K A (productRadii s t) (g * h) (numerators K A g h f k)
    (generatesUnitIdeal K A g h f k hf hk)).trans (locus_eq_inter K A s t g h f k hf hk)

theorem isClosedEmbedding_baseSpectrumMap
    (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    Topology.IsClosedEmbedding (baseSpectrumMap K A s t g h f k) :=
  isClosedEmbedding_spectrumMap K A (productRadii s t) (g * h) (numerators K A g h f k)
    (generatesUnitIdeal K A g h f k hf hk)

/-- The spectrum of the actual product quotient, identified with the intersection. -/
def intersectionHomeomorph (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    BanachSpectrum (Algebra K A s t g h f k) ≃ₜ ↥(locus K A s g f ∩ locus K A t h k) :=
  (isClosedEmbedding_baseSpectrumMap K A s t g h f k hf hk).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_baseSpectrumMap K A s t g h f k hf hk))

@[simp] theorem intersectionHomeomorph_apply_coe
    (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k)
    (x : BanachSpectrum (Algebra K A s t g h f k)) :
    (intersectionHomeomorph K A s t g h f k hf hk x).val = baseSpectrumMap K A s t g h f k x := rfl

variable [CompleteSpace K]
  (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k)

/-- Construct the contractive restriction from the left scalar rational quotient. -/
def leftMap : BoundedAlgHom K (algebra K A s g f) (Algebra K A s t g h f k) :=
  (RelativeRationalPresentation.evaluate K A s (presentationMap K A g)
    (fun i => presentationMap K A (f i)) (Algebra K A s t g h f k)
    (base K A s t g h f k) (leftCoordinate K A s t g h f k)
    (norm_base_le K A s t g h f k) (leftCoordinate_monomial K A s t g h f k)
    (leftCoordinate_equation K A s t g h f k hf hk)).comp
      (relativeEquiv K A s g f).toBoundedAlgHom

/-- Construct the contractive restriction from the right scalar rational quotient. -/
def rightMap : BoundedAlgHom K (algebra K A t h k) (Algebra K A s t g h f k) :=
  (RelativeRationalPresentation.evaluate K A t (presentationMap K A h)
    (fun j => presentationMap K A (k j)) (Algebra K A s t g h f k)
    (base K A s t g h f k) (rightCoordinate K A s t g h f k)
    (norm_base_le K A s t g h f k) (rightCoordinate_monomial K A s t g h f k)
    (rightCoordinate_equation K A s t g h f k hf hk)).comp
      (relativeEquiv K A t h k).toBoundedAlgHom

@[simp] theorem leftMap_base (a : A) :
    leftMap K A s t g h f k hf hk (baseMap K A s g f a) = base K A s t g h f k a := by
  simp only [leftMap, BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    relativeEquiv_baseMap, RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem rightMap_base (a : A) :
    rightMap K A s t g h f k hf hk (baseMap K A t h k a) = base K A s t g h f k a := by
  simp only [rightMap, BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    relativeEquiv_baseMap, RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem leftMap_fraction (i : Fin m) :
    leftMap K A s t g h f k hf hk (fraction K A s g f i) = leftCoordinate K A s t g h f k i := by
  simp only [leftMap, BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    relativeEquiv_fraction, RelativeRationalPresentation.evaluate_fraction]

@[simp] theorem rightMap_fraction (j : Fin n) :
    rightMap K A s t g h f k hf hk (fraction K A t h k j) = rightCoordinate K A s t g h f k j := by
  simp only [rightMap, BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    relativeEquiv_fraction, RelativeRationalPresentation.evaluate_fraction]

theorem norm_leftMap_le (a : algebra K A s g f) :
    ‖leftMap K A s t g h f k hf hk a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A s (presentationMap K A g)
    (fun i => presentationMap K A (f i)) (Algebra K A s t g h f k)
    (base K A s t g h f k) (leftCoordinate K A s t g h f k)
    (norm_base_le K A s t g h f k) (leftCoordinate_monomial K A s t g h f k)
    (leftCoordinate_equation K A s t g h f k hf hk) _).trans_eq
      (norm_relativeEquiv K A s g f a)

theorem norm_rightMap_le (a : algebra K A t h k) :
    ‖rightMap K A s t g h f k hf hk a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A t (presentationMap K A h)
    (fun j => presentationMap K A (k j)) (Algebra K A s t g h f k)
    (base K A s t g h f k) (rightCoordinate K A s t g h f k)
    (norm_base_le K A s t g h f k) (rightCoordinate_monomial K A s t g h f k)
    (rightCoordinate_equation K A s t g h f k hf hk) _).trans_eq
      (norm_relativeEquiv K A t h k a)

theorem leftMap_comp_baseMap :
    (leftMap K A s t g h f k hf hk).comp (baseMap K A s g f) = base K A s t g h f k := by
  apply BoundedAlgHom.ext
  exact leftMap_base K A s t g h f k hf hk

theorem rightMap_comp_baseMap :
    (rightMap K A s t g h f k hf hk).comp (baseMap K A t h k) = base K A s t g h f k := by
  apply BoundedAlgHom.ext
  exact rightMap_base K A s t g h f k hf hk

/-- The actual contravariant spectrum map to the left quotient spectrum. -/
def leftSpectrumMap : C(BanachSpectrum (Algebra K A s t g h f k), BanachSpectrum (algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (leftMap K A s t g h f k hf hk).toBoundedRingHom

/-- The actual contravariant spectrum map to the right quotient spectrum. -/
def rightSpectrumMap : C(BanachSpectrum (Algebra K A s t g h f k), BanachSpectrum (algebra K A t h k)) :=
  BanachSpectrum.comapContinuous (rightMap K A s t g h f k hf hk).toBoundedRingHom

theorem leftSpectrumMap_naturality :
    (spectrumMap K A s g f).comp (leftSpectrumMap K A s t g h f k hf hk) =
      baseSpectrumMap K A s t g h f k := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (leftMap K A s t g h f k hf hk (baseMap K A s g f a)) = x (base K A s t g h f k a)
  rw [leftMap_base]

theorem rightSpectrumMap_naturality :
    (spectrumMap K A t h k).comp (rightSpectrumMap K A s t g h f k hf hk) =
      baseSpectrumMap K A s t g h f k := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (rightMap K A s t g h f k hf hk (baseMap K A t h k a)) = x (base K A s t g h f k a)
  rw [rightMap_base]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection
