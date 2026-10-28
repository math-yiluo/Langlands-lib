import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectrum

/-! # A Weierstrass quotient over an actual positive-radius rational quotient -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalWeierstrassIntersection

open GeneralizedTateAlgebra

section ScalarEvaluation

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {k : ℕ} (r : PositivePolyradius (Fin k))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (q : Fin k → GeneralizedTateAlgebra A.polyradius K)
  (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]
  (φ : BoundedAlgHom K A B) (b : Fin k → B)
  (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
  (hb : ∀ d : Fin k →₀ ℕ,
    ‖StrictTateAlgebra.monomialValue _ B b d‖ ≤ r.weight d)
  (hq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (q j)))

private def scalarEvaluate : BoundedAlgHom K (algebra K A r g q) B :=
  (RelativeRationalPresentation.evaluate K A r (presentationMap K A g)
    (fun j => presentationMap K A (q j)) B φ b hφ hb
    hq).comp
      (relativeEquiv K A r g q).toBoundedAlgHom

@[simp] private theorem scalarEvaluate_base (a : A) :
    scalarEvaluate K A r g q B φ b hφ hb hq (baseMap K A r g q a) = φ a := by
  simp only [scalarEvaluate, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]

@[simp] private theorem scalarEvaluate_fraction (j : Fin k) :
    scalarEvaluate K A r g q B φ b hφ hb hq (fraction K A r g q j) = b j := by
  simp only [scalarEvaluate, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_fraction,
    RelativeRationalPresentation.evaluate_fraction]

private theorem norm_scalarEvaluate_le (a : algebra K A r g q) :
    ‖scalarEvaluate K A r g q B φ b hφ hb hq a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A r (presentationMap K A g)
    (fun j => presentationMap K A (q j)) B φ b hφ hb
    hq _).trans_eq
      (norm_relativeEquiv K A r g q a)

end ScalarEvaluation

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m n : ℕ}
  (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (h : Fin n → GeneralizedTateAlgebra A.polyradius K)

/-- The scalar quotient imposing the first tuple of inequalities. -/
abbrev firstAlgebra : PresentedAffinoidAlgebra K := algebra K A s g f

/-- The second tuple, as actual elements of the first quotient. -/
def secondTuple (j : Fin n) : firstAlgebra K A s g f :=
  baseMap K A s g f (presentationMap K A (h j))

/-- The actual relative Weierstrass quotient over the first quotient. -/
abbrev Algebra :=
  RelativeRationalPresentation.WeierstrassAlgebra K (firstAlgebra K A s g f) t
    (secondTuple K A s g f h)

/-- The single common-denominator tuple for the mixed intersection. -/
def combinedNumerators : Fin (m + n) → GeneralizedTateAlgebra A.polyradius K :=
  Fin.append f (fun j => g * h j)

/-- The scalar rational quotient on the mixed common-denominator tuple. -/
abbrev combinedAlgebra : PresentedAffinoidAlgebra K :=
  algebra K A (s.append t) g (combinedNumerators K A g f h)

/-- The coefficient map of the second quotient. -/
def iteratedBase : BoundedAlgHom K (firstAlgebra K A s g f) (Algebra K A s t g f h) :=
  RelativeRationalPresentation.baseMap K (firstAlgebra K A s g f) t 1
    (secondTuple K A s g f h)

/-- The composite structural map from the original coefficient algebra. -/
def base : BoundedAlgHom K A (Algebra K A s t g f h) :=
  (iteratedBase K A s t g f h).comp (baseMap K A s g f)

/-- The old coordinate, mapped into the second quotient. -/
def leftCoordinate (i : Fin m) : Algebra K A s t g f h :=
  iteratedBase K A s t g f h (fraction K A s g f i)

/-- The newly adjoined coordinate of the second quotient. -/
def rightCoordinate (j : Fin n) : Algebra K A s t g f h :=
  RelativeRationalPresentation.fraction K (firstAlgebra K A s g f) t 1
    (secondTuple K A s g f h) j

theorem norm_iteratedBase_le (a : firstAlgebra K A s g f) :
    ‖iteratedBase K A s t g f h a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_baseMap_le K (firstAlgebra K A s g f) t 1
    (secondTuple K A s g f h) a

theorem norm_base_le (a : A) : ‖base K A s t g f h a‖ ≤ ‖a‖ :=
  (norm_iteratedBase_le K A s t g f h _).trans (norm_baseMap_le K A s g f a)

theorem leftCoordinate_equation (i : Fin m) :
    base K A s t g f h (presentationMap K A g) * leftCoordinate K A s t g f h i =
      base K A s t g f h (presentationMap K A (f i)) := by
  change iteratedBase K A s t g f h (baseMap K A s g f (presentationMap K A g)) *
    iteratedBase K A s t g f h (fraction K A s g f i) = _
  rw [← map_mul, fraction_equation]
  rfl

theorem rightCoordinate_eq_base (j : Fin n) :
    rightCoordinate K A s t g f h j = base K A s t g f h (presentationMap K A (h j)) :=
  RelativeRationalPresentation.weierstrass_fraction K (firstAlgebra K A s g f) t
    (secondTuple K A s g f h) j

theorem norm_leftCoordinate_le (i : Fin m) :
    ‖leftCoordinate K A s t g f h i‖ ≤ s i :=
  (norm_iteratedBase_le K A s t g f h _).trans (norm_fraction_le K A s g f i)

theorem norm_rightCoordinate_le (j : Fin n) :
    ‖rightCoordinate K A s t g f h j‖ ≤ t j :=
  RelativeRationalPresentation.norm_fraction_le K (firstAlgebra K A s g f) t 1
    (secondTuple K A s g f h) j

/-- The original denominator and numerators still generate after adjoining a block. -/
theorem combined_generates (hunit : GeneratesUnitIdeal K A g f) :
    GeneratesUnitIdeal K A g (combinedNumerators K A g f h) := by
  apply le_antisymm le_top
  rw [← hunit]
  apply Ideal.span_mono
  intro a ha
  rcases ha with rfl | ⟨i, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Fin.castAdd n i, by simp only [combinedNumerators, Fin.append_left]⟩

/-- Positive denominator cancellation identifies the mixed inequality locus. -/
theorem combinedLocus_eq_inter (hunit : GeneratesUnitIdeal K A g f) :
    locus K A (s.append t) g (combinedNumerators K A g f h) =
      locus K A s g f ∩ weierstrassLocus K A t h := by
  ext x
  constructor
  · intro hx
    have hf : x ∈ locus K A s g f := fun i => by
      simpa only [combinedNumerators, Fin.append_left, PositivePolyradius.append_castAdd]
        using hx (Fin.castAdd n i)
    have hgpos : 0 < x (presentationMap K A g) :=
      lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
        (denominator_ne_zero K A s g f hunit x hf).symm
    refine ⟨hf, fun j => ?_⟩
    apply (mul_le_mul_iff_right₀ hgpos).mp
    have hj : x (presentationMap K A g) * x (presentationMap K A (h j)) ≤
        t j * x (presentationMap K A g) := by
      simpa only [combinedNumerators, Fin.append_right, PositivePolyradius.append_natAdd,
        map_mul] using hx (Fin.natAdd m j)
    exact hj.trans_eq (mul_comm _ _)
  · rintro ⟨hf, hh⟩ k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [combinedNumerators, Fin.append_left, PositivePolyradius.append_castAdd]
        using hf i
    · simp only [combinedNumerators, Fin.append_right, PositivePolyradius.append_natAdd,
        map_mul]
      exact (mul_le_mul_of_nonneg_left (hh j)
        (apply_nonneg x.toMulRingSeminorm _)).trans_eq (mul_comm _ _)

private def combinedTuple : Fin (m + n) → Algebra K A s t g f h :=
  Fin.append (leftCoordinate K A s t g f h) (rightCoordinate K A s t g f h)

private theorem combinedTuple_norm (k : Fin (m + n)) :
    ‖combinedTuple K A s t g f h k‖ ≤ (s.append t) k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedTuple, Fin.append_left, PositivePolyradius.append_castAdd] using
      norm_leftCoordinate_le K A s t g f h i
  · simpa only [combinedTuple, Fin.append_right, PositivePolyradius.append_natAdd] using
      norm_rightCoordinate_le K A s t g f h j

private theorem combinedTuple_equations (k : Fin (m + n)) :
    base K A s t g f h (presentationMap K A g) * combinedTuple K A s t g f h k =
      base K A s t g f h (presentationMap K A (combinedNumerators K A g f h k)) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedTuple, combinedNumerators, Fin.append_left] using
      leftCoordinate_equation K A s t g f h i
  · simp only [combinedTuple, combinedNumerators, Fin.append_right, map_mul,
      rightCoordinate_eq_base]

private theorem iterated_unit_norm : ‖(1 : Algebra K A s t g f h)‖ ≤ 1 := by
  have h1 := norm_iteratedBase_le K A s t g f h 1
  rw [map_one] at h1
  exact h1.trans (PresentedAffinoidAlgebra.norm_one_le K (firstAlgebra K A s g f))

private theorem combinedTuple_monomial (d : Fin (m + n) →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A s t g f h)
      (combinedTuple K A s t g f h) d‖ ≤ (s.append t).weight d :=
  monomialValue_norm_le_weight (s.append t) (Algebra K A s t g f h)
    (iterated_unit_norm K A s t g f h) (combinedTuple K A s t g f h)
    (combinedTuple_norm K A s t g f h) d

/-- The left block coordinate in the combined quotient. -/
def combinedLeft (i : Fin m) : combinedAlgebra K A s t g f h :=
  fraction K A (s.append t) g (combinedNumerators K A g f h) (Fin.castAdd n i)

/-- The right block coordinate in the combined quotient. -/
def combinedRight (j : Fin n) : combinedAlgebra K A s t g f h :=
  fraction K A (s.append t) g (combinedNumerators K A g f h) (Fin.natAdd m j)

private theorem norm_combinedLeft (i : Fin m) :
    ‖combinedLeft K A s t g f h i‖ ≤ s i := by
  simpa only [combinedLeft, PositivePolyradius.append_castAdd] using
    norm_fraction_le K A (s.append t) g (combinedNumerators K A g f h) (Fin.castAdd n i)

private theorem norm_combinedRight (j : Fin n) :
    ‖combinedRight K A s t g f h j‖ ≤ t j := by
  simpa only [combinedRight, PositivePolyradius.append_natAdd] using
    norm_fraction_le K A (s.append t) g (combinedNumerators K A g f h) (Fin.natAdd m j)

private theorem combinedLeft_monomial (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (combinedAlgebra K A s t g f h)
      (combinedLeft K A s t g f h) d‖ ≤ s.weight d :=
  monomialValue_norm_le_weight s (combinedAlgebra K A s t g f h)
    (PresentedAffinoidAlgebra.norm_one_le K (combinedAlgebra K A s t g f h))
    (combinedLeft K A s t g f h) (norm_combinedLeft K A s t g f h) d

private theorem combinedRight_monomial (d : Fin n →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (combinedAlgebra K A s t g f h)
      (combinedRight K A s t g f h) d‖ ≤ t.weight d :=
  monomialValue_norm_le_weight t (combinedAlgebra K A s t g f h)
    (PresentedAffinoidAlgebra.norm_one_le K (combinedAlgebra K A s t g f h))
    (combinedRight K A s t g f h) (norm_combinedRight K A s t g f h) d

private theorem combinedLeft_equations (i : Fin m) :
    baseMap K A (s.append t) g (combinedNumerators K A g f h) (presentationMap K A g) *
      combinedLeft K A s t g f h i =
      baseMap K A (s.append t) g (combinedNumerators K A g f h) (presentationMap K A (f i)) := by
  have hq := fraction_equation K A (s.append t) g (combinedNumerators K A g f h)
    (Fin.castAdd n i)
  rw [show combinedNumerators K A g f h (Fin.castAdd n i) = f i from
    Fin.append_left f (fun j => g * h j) i] at hq
  exact hq

private theorem combinedRight_equations (hunit : GeneratesUnitIdeal K A g f) (j : Fin n) :
    combinedRight K A s t g f h j =
      baseMap K A (s.append t) g (combinedNumerators K A g f h) (presentationMap K A (h j)) := by
  apply (isUnit_baseMap_denominator K A (s.append t) g (combinedNumerators K A g f h)
    (combined_generates K A g f h hunit)).mul_left_cancel
  have hq := fraction_equation K A (s.append t) g (combinedNumerators K A g f h)
    (Fin.natAdd m j)
  rw [show combinedNumerators K A g f h (Fin.natAdd m j) = g * h j from
    Fin.append_right f (fun j => g * h j) j] at hq
  simpa only [combinedRight, map_mul] using hq

variable [CompleteSpace K]

/-- Evaluate the single combined quotient in the actual iterated quotient. -/
def fromCombined : BoundedAlgHom K (combinedAlgebra K A s t g f h) (Algebra K A s t g f h) :=
  scalarEvaluate K A (s.append t) g (combinedNumerators K A g f h) (Algebra K A s t g f h)
    (base K A s t g f h) (combinedTuple K A s t g f h)
    (norm_base_le K A s t g f h) (combinedTuple_monomial K A s t g f h)
    (combinedTuple_equations K A s t g f h)

@[simp] theorem fromCombined_base (a : A) :
    fromCombined K A s t g f h (baseMap K A (s.append t) g (combinedNumerators K A g f h) a) =
      base K A s t g f h a := scalarEvaluate_base _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem fromCombined_left (i : Fin m) :
    fromCombined K A s t g f h (combinedLeft K A s t g f h i) =
      leftCoordinate K A s t g f h i := by
  simp only [fromCombined, combinedLeft, scalarEvaluate_fraction, combinedTuple, Fin.append_left]

@[simp] theorem fromCombined_right (j : Fin n) :
    fromCombined K A s t g f h (combinedRight K A s t g f h j) =
      rightCoordinate K A s t g f h j := by
  simp only [fromCombined, combinedRight, scalarEvaluate_fraction, combinedTuple, Fin.append_right]

theorem norm_fromCombined_le (a : combinedAlgebra K A s t g f h) :
    ‖fromCombined K A s t g f h a‖ ≤ ‖a‖ :=
  norm_scalarEvaluate_le _ _ _ _ _ _ _ _ _ _ _ _

/-- The actual map from the first quotient to the combined quotient. -/
def firstMap : BoundedAlgHom K (firstAlgebra K A s g f) (combinedAlgebra K A s t g f h) :=
  scalarEvaluate K A s g f (combinedAlgebra K A s t g f h)
    (baseMap K A (s.append t) g (combinedNumerators K A g f h)) (combinedLeft K A s t g f h)
    (norm_baseMap_le K A (s.append t) g (combinedNumerators K A g f h))
    (combinedLeft_monomial K A s t g f h) (combinedLeft_equations K A s t g f h)

@[simp] theorem firstMap_base (a : A) :
    firstMap K A s t g f h (baseMap K A s g f a) =
      baseMap K A (s.append t) g (combinedNumerators K A g f h) a :=
  scalarEvaluate_base _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem firstMap_fraction (i : Fin m) :
    firstMap K A s t g f h (fraction K A s g f i) = combinedLeft K A s t g f h i :=
  scalarEvaluate_fraction _ _ _ _ _ _ _ _ _ _ _ _

theorem norm_firstMap_le (a : firstAlgebra K A s g f) :
    ‖firstMap K A s t g f h a‖ ≤ ‖a‖ := norm_scalarEvaluate_le _ _ _ _ _ _ _ _ _ _ _ _

variable (hunit : GeneratesUnitIdeal K A g f)

include hunit in
private theorem toCombined_equations (j : Fin n) :
    firstMap K A s t g f h 1 * combinedRight K A s t g f h j =
      firstMap K A s t g f h (secondTuple K A s g f h j) := by
  rw [map_one, one_mul, secondTuple, firstMap_base, combinedRight_equations K A s t g f h hunit]

/-- Evaluate the second quotient using the first quotient map and the right block. -/
def toCombined : BoundedAlgHom K (Algebra K A s t g f h) (combinedAlgebra K A s t g f h) :=
  RelativeRationalPresentation.evaluate K (firstAlgebra K A s g f) t 1
    (secondTuple K A s g f h) (combinedAlgebra K A s t g f h)
    (firstMap K A s t g f h) (combinedRight K A s t g f h)
    (norm_firstMap_le K A s t g f h) (combinedRight_monomial K A s t g f h)
    (toCombined_equations K A s t g f h hunit)

@[simp] theorem toCombined_iteratedBase (a : firstAlgebra K A s g f) :
    toCombined K A s t g f h hunit (iteratedBase K A s t g f h a) = firstMap K A s t g f h a :=
  RelativeRationalPresentation.evaluate_baseMap _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem toCombined_base (a : A) :
    toCombined K A s t g f h hunit (base K A s t g f h a) =
      baseMap K A (s.append t) g (combinedNumerators K A g f h) a := by
  change toCombined K A s t g f h hunit (iteratedBase K A s t g f h (baseMap K A s g f a)) = _
  rw [toCombined_iteratedBase, firstMap_base]

@[simp] theorem toCombined_left (i : Fin m) :
    toCombined K A s t g f h hunit (leftCoordinate K A s t g f h i) =
      combinedLeft K A s t g f h i := by
  change toCombined K A s t g f h hunit (iteratedBase K A s t g f h (fraction K A s g f i)) = _
  rw [toCombined_iteratedBase, firstMap_fraction]

@[simp] theorem toCombined_right (j : Fin n) :
    toCombined K A s t g f h hunit (rightCoordinate K A s t g f h j) =
      combinedRight K A s t g f h j :=
  RelativeRationalPresentation.evaluate_fraction _ _ _ _ _ _ _ _ _ _ _ _

theorem norm_toCombined_le (a : Algebra K A s t g f h) :
    ‖toCombined K A s t g f h hunit a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le _ _ _ _ _ _ _ _ _ _ _ _


/-- The reverse evaluation extends the second quotient's coefficient map. -/
theorem fromCombined_comp_firstMap :
    (fromCombined K A s t g f h).comp (firstMap K A s t g f h) =
      iteratedBase K A s t g f h := by
  apply hom_ext K A s g f (Algebra K A s t g f h)
  · intro a
    change fromCombined K A s t g f h
      (firstMap K A s t g f h (baseMap K A s g f a)) =
        iteratedBase K A s t g f h (baseMap K A s g f a)
    rw [firstMap_base, fromCombined_base]
    rfl
  · intro i
    change fromCombined K A s t g f h (firstMap K A s t g f h (fraction K A s g f i)) =
      leftCoordinate K A s t g f h i
    rw [firstMap_fraction, fromCombined_left]

theorem fromCombined_toCombined (a : Algebra K A s t g f h) :
    fromCombined K A s t g f h (toCombined K A s t g f h hunit a) = a := by
  have heq : (fromCombined K A s t g f h).comp (toCombined K A s t g f h hunit) =
      BoundedAlgHom.id K (Algebra K A s t g f h) := by
    apply RelativeRationalPresentation.hom_ext K (firstAlgebra K A s g f) t 1
      (secondTuple K A s g f h) (Algebra K A s t g f h)
    · intro b
      change fromCombined K A s t g f h
        (toCombined K A s t g f h hunit (iteratedBase K A s t g f h b)) =
          iteratedBase K A s t g f h b
      rw [toCombined_iteratedBase]
      exact congrArg (fun ψ : BoundedAlgHom K (firstAlgebra K A s g f)
        (Algebra K A s t g f h) => ψ b) (fromCombined_comp_firstMap K A s t g f h)
    · intro j
      change fromCombined K A s t g f h
        (toCombined K A s t g f h hunit (rightCoordinate K A s t g f h j)) =
          rightCoordinate K A s t g f h j
      rw [toCombined_right, fromCombined_right]
  exact congrArg (fun ψ : BoundedAlgHom K (Algebra K A s t g f h)
    (Algebra K A s t g f h) => ψ a) heq

theorem toCombined_fromCombined (a : combinedAlgebra K A s t g f h) :
    toCombined K A s t g f h hunit (fromCombined K A s t g f h a) = a := by
  have heq : (toCombined K A s t g f h hunit).comp (fromCombined K A s t g f h) =
      BoundedAlgHom.id K (combinedAlgebra K A s t g f h) := by
    apply hom_ext K A (s.append t) g (combinedNumerators K A g f h) (combinedAlgebra K A s t g f h)
    · intro b
      change toCombined K A s t g f h hunit
        (fromCombined K A s t g f h (baseMap K A (s.append t) g (combinedNumerators K A g f h) b)) = _
      rw [fromCombined_base, toCombined_base]
      rfl
    · intro k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · change toCombined K A s t g f h hunit
          (fromCombined K A s t g f h (combinedLeft K A s t g f h i)) =
            combinedLeft K A s t g f h i
        rw [fromCombined_left, toCombined_left]
      · change toCombined K A s t g f h hunit
          (fromCombined K A s t g f h (combinedRight K A s t g f h j)) =
            combinedRight K A s t g f h j
        rw [fromCombined_right, toCombined_right]
  exact congrArg (fun ψ : BoundedAlgHom K (combinedAlgebra K A s t g f h)
    (combinedAlgebra K A s t g f h) => ψ a) heq

/-- A rational quotient followed by a Weierstrass quotient combines into the
common-denominator scalar quotient. Both inverses are constructed. -/
def equiv : BoundedAlgEquiv K (Algebra K A s t g f h) (combinedAlgebra K A s t g f h) :=
  BoundedAlgEquiv.ofHomInv (toCombined K A s t g f h hunit) (fromCombined K A s t g f h)
    (fromCombined_toCombined K A s t g f h hunit) (toCombined_fromCombined K A s t g f h hunit)

@[simp] theorem equiv_iteratedBase (a : firstAlgebra K A s g f) :
    equiv K A s t g f h hunit (iteratedBase K A s t g f h a) = firstMap K A s t g f h a :=
  toCombined_iteratedBase K A s t g f h hunit a

@[simp] theorem equiv_base (a : A) :
    equiv K A s t g f h hunit (base K A s t g f h a) =
      baseMap K A (s.append t) g (combinedNumerators K A g f h) a :=
  toCombined_base K A s t g f h hunit a

@[simp] theorem equiv_left (i : Fin m) :
    equiv K A s t g f h hunit (leftCoordinate K A s t g f h i) = combinedLeft K A s t g f h i :=
  toCombined_left K A s t g f h hunit i

@[simp] theorem equiv_right (j : Fin n) :
    equiv K A s t g f h hunit (rightCoordinate K A s t g f h j) = combinedRight K A s t g f h j :=
  toCombined_right K A s t g f h hunit j

/-- Both actual quotient norms agree, since the two constructed maps contract. -/
theorem norm_equiv (a : Algebra K A s t g f h) :
    ‖equiv K A s t g f h hunit a‖ = ‖a‖ := by
  apply le_antisymm (norm_toCombined_le K A s t g f h hunit a)
  calc
    ‖a‖ = ‖fromCombined K A s t g f h (toCombined K A s t g f h hunit a)‖ :=
      congrArg norm (fromCombined_toCombined K A s t g f h hunit a).symm
    _ ≤ ‖toCombined K A s t g f h hunit a‖ := norm_fromCombined_le K A s t g f h _

theorem norm_equiv_symm (a : combinedAlgebra K A s t g f h) :
    ‖(equiv K A s t g f h hunit).symm a‖ = ‖a‖ := by
  have heq := norm_equiv K A s t g f h hunit ((equiv K A s t g f h hunit).symm a)
  rw [BoundedAlgEquiv.apply_symm_apply] at heq
  exact heq.symm

theorem isometry_equiv : Isometry (equiv K A s t g f h hunit) :=
  AddMonoidHomClass.isometry_of_norm (equiv K A s t g f h hunit).toAlgEquiv
    (norm_equiv K A s t g f h hunit)

/-- The actual spectrum pullback of the second quotient's coefficient map. -/
def iteratedSpectrumMap :
    C(BanachSpectrum (Algebra K A s t g f h), BanachSpectrum (firstAlgebra K A s g f)) :=
  BanachSpectrum.comapContinuous (iteratedBase K A s t g f h).toBoundedRingHom

/-- The combined quotient's spectrum map to the first quotient spectrum. -/
def firstSpectrumMap :
    C(BanachSpectrum (combinedAlgebra K A s t g f h), BanachSpectrum (firstAlgebra K A s g f)) :=
  BanachSpectrum.comapContinuous (firstMap K A s t g f h).toBoundedRingHom

/-- The actual structural map to the original coefficient spectrum. -/
def baseSpectrumMap : C(BanachSpectrum (Algebra K A s t g f h), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (base K A s t g f h).toBoundedRingHom

/-- Contravariant spectrum homeomorphism induced by the constructed equivalence. -/
def spectrumHomeomorph :
    BanachSpectrum (combinedAlgebra K A s t g f h) ≃ₜ BanachSpectrum (Algebra K A s t g f h) :=
  (equiv K A s t g f h hunit).spectrumHomeomorph

@[simp] theorem spectrumHomeomorph_apply (x : BanachSpectrum (combinedAlgebra K A s t g f h))
    (a : Algebra K A s t g f h) :
    spectrumHomeomorph K A s t g f h hunit x a = x (equiv K A s t g f h hunit a) := rfl

/-- The homeomorphism respects the structural maps to the first quotient spectrum. -/
theorem spectrumHomeomorph_naturality :
    (iteratedSpectrumMap K A s t g f h).comp
      ⟨spectrumHomeomorph K A s t g f h hunit, (spectrumHomeomorph K A s t g f h hunit).continuous⟩ =
        firstSpectrumMap K A s t g f h := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (equiv K A s t g f h hunit (iteratedBase K A s t g f h a)) = x (firstMap K A s t g f h a)
  rw [equiv_iteratedBase]

@[simp] theorem baseSpectrumMap_homeomorph (x : BanachSpectrum (combinedAlgebra K A s t g f h)) :
    baseSpectrumMap K A s t g f h (spectrumHomeomorph K A s t g f h hunit x) =
      spectrumMap K A (s.append t) g (combinedNumerators K A g f h) x := by
  apply BanachSpectrum.ext
  intro a
  change x (equiv K A s t g f h hunit (base K A s t g f h a)) =
    x (baseMap K A (s.append t) g (combinedNumerators K A g f h) a)
  rw [equiv_base]

@[simp] theorem spectrumMap_homeomorph_symm (x : BanachSpectrum (Algebra K A s t g f h)) :
    spectrumMap K A (s.append t) g (combinedNumerators K A g f h)
      ((spectrumHomeomorph K A s t g f h hunit).symm x) = baseSpectrumMap K A s t g f h x := by
  have heq := baseSpectrumMap_homeomorph K A s t g f h hunit ((spectrumHomeomorph K A s t g f h hunit).symm x)
  rw [Homeomorph.apply_symm_apply] at heq
  exact heq.symm

include hunit in
/-- The iterated quotient has exactly the intersection of the original rational
and Weierstrass inequality loci as its structural spectrum image. -/
theorem range_baseSpectrumMap :
    Set.range (baseSpectrumMap K A s t g f h) =
      locus K A s g f ∩ weierstrassLocus K A t h := by
  have hr := range_spectrumMap K A (s.append t) g (combinedNumerators K A g f h)
    (combined_generates K A g f h hunit)
  rw [combinedLocus_eq_inter K A s t g f h hunit] at hr
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [← hr]
    exact ⟨(spectrumHomeomorph K A s t g f h hunit).symm y,
      spectrumMap_homeomorph_symm K A s t g f h hunit y⟩
  · intro hx
    have hx' : x ∈ Set.range
        (spectrumMap K A (s.append t) g (combinedNumerators K A g f h)) := by
      rwa [hr]
    obtain ⟨y, hy⟩ := hx'
    exact ⟨spectrumHomeomorph K A s t g f h hunit y,
      (baseSpectrumMap_homeomorph K A s t g f h hunit y).trans hy⟩

include hunit in
theorem isClosedEmbedding_baseSpectrumMap :
    Topology.IsClosedEmbedding (baseSpectrumMap K A s t g f h) := by
  apply (baseSpectrumMap K A s t g f h).continuous.isClosedEmbedding
  intro x y hxy
  apply (spectrumHomeomorph K A s t g f h hunit).symm.injective
  apply spectrumMap_injective K A (s.append t) g (combinedNumerators K A g f h)
    (combined_generates K A g f h hunit)
  rw [spectrumMap_homeomorph_symm, spectrumMap_homeomorph_symm, hxy]

/-- The spectrum of the actual iterated quotient, identified with the
rational-Weierstrass intersection by its structural map. -/
def intersectionHomeomorph :
    BanachSpectrum (Algebra K A s t g f h) ≃ₜ
      ↥(locus K A s g f ∩ weierstrassLocus K A t h) :=
  (isClosedEmbedding_baseSpectrumMap K A s t g f h hunit).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_baseSpectrumMap K A s t g f h hunit))

@[simp] theorem intersectionHomeomorph_apply_coe
    (x : BanachSpectrum (Algebra K A s t g f h)) :
    (intersectionHomeomorph K A s t g f h hunit x).val =
      baseSpectrumMap K A s t g f h x := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalWeierstrassIntersection
