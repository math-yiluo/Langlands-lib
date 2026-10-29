import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersection

/-! # Isometric comparison of iterated and product rational intersections -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersectionIterated

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m n : ℕ}
  (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
  (g h : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (k : Fin n → GeneralizedTateAlgebra A.polyradius K)

/-- The actual intrinsic rational quotient over the first scalar rational quotient. -/
abbrev Algebra :=
  RelativeRationalPresentation.Algebra K (algebra K A s g f) t
    (baseMap K A s g f (presentationMap K A h))
    (fun j => baseMap K A s g f (presentationMap K A (k j)))

/-- The actual coefficient map from the first rational quotient. -/
def coefficientMap : BoundedAlgHom K (algebra K A s g f) (Algebra K A s t g h f k) :=
  RelativeRationalPresentation.baseMap K (algebra K A s g f) t
    (baseMap K A s g f (presentationMap K A h))
    (fun j => baseMap K A s g f (presentationMap K A (k j)))

/-- The composite coefficient map from the original presented algebra. -/
def base : BoundedAlgHom K A (Algebra K A s t g h f k) :=
  (coefficientMap K A s t g h f k).comp (baseMap K A s g f)

@[simp] theorem coefficientMap_baseMap (a : A) :
    coefficientMap K A s t g h f k (baseMap K A s g f a) = base K A s t g h f k a := rfl

theorem norm_coefficientMap_le (b : algebra K A s g f) :
    ‖coefficientMap K A s t g h f k b‖ ≤ ‖b‖ :=
  RelativeRationalPresentation.norm_baseMap_le K (algebra K A s g f) t _ _ b

theorem norm_base_le (a : A) : ‖base K A s t g h f k a‖ ≤ ‖a‖ :=
  (norm_coefficientMap_le K A s t g h f k _).trans (norm_baseMap_le K A s g f a)

/-- The old fractions, mapped into the actual intrinsic quotient. -/
def leftFraction (i : Fin m) : Algebra K A s t g h f k :=
  coefficientMap K A s t g h f k (fraction K A s g f i)

/-- The new fractions of the actual intrinsic quotient. -/
def rightFraction (j : Fin n) : Algebra K A s t g h f k :=
  RelativeRationalPresentation.fraction K (algebra K A s g f) t
    (baseMap K A s g f (presentationMap K A h))
    (fun j => baseMap K A s g f (presentationMap K A (k j))) j

theorem norm_leftFraction_le (i : Fin m) : ‖leftFraction K A s t g h f k i‖ ≤ s i :=
  (norm_coefficientMap_le K A s t g h f k _).trans (norm_fraction_le K A s g f i)

theorem norm_rightFraction_le (j : Fin n) : ‖rightFraction K A s t g h f k j‖ ≤ t j :=
  RelativeRationalPresentation.norm_fraction_le K (algebra K A s g f) t _ _ j

theorem leftFraction_equation (i : Fin m) :
    base K A s t g h f k (presentationMap K A g) * leftFraction K A s t g h f k i =
      base K A s t g h f k (presentationMap K A (f i)) := by
  simpa only [← coefficientMap_baseMap, leftFraction, map_mul] using
    congrArg (coefficientMap K A s t g h f k) (fraction_equation K A s g f i)

theorem rightFraction_equation (j : Fin n) :
    base K A s t g h f k (presentationMap K A h) * rightFraction K A s t g h f k j =
      base K A s t g h f k (presentationMap K A (k j)) :=
  RelativeRationalPresentation.fraction_equation K (algebra K A s g f) t _ _ j

/-- The actual intrinsic quotient retains a unit norm bound even when it is zero. -/
theorem norm_one_le : ‖(1 : Algebra K A s t g h f k)‖ ≤ 1 := by
  calc
    _ = ‖coefficientMap K A s t g h f k 1‖ := by rw [map_one]
    _ ≤ ‖(1 : algebra K A s g f)‖ := norm_coefficientMap_le K A s t g h f k 1
    _ ≤ 1 := PresentedAffinoidAlgebra.norm_one_le K (algebra K A s g f)

/-- Every product of the denominator-extended fraction tuples in the iterated quotient. -/
def productFraction : Fin ((m + 1) * (n + 1)) → Algebra K A s t g h f k := fun a =>
  (Fin.cons 1 (leftFraction K A s t g h f k) : Fin (m + 1) → _) (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 (rightFraction K A s t g h f k) : Fin (n + 1) → _) (finProdFinEquiv.symm a).2

@[simp] theorem productFraction_pair (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productFraction K A s t g h f k (finProdFinEquiv (i, j)) =
      (Fin.cons 1 (leftFraction K A s t g h f k) : Fin (m + 1) → _) i *
        (Fin.cons 1 (rightFraction K A s t g h f k) : Fin (n + 1) → _) j := by
  simp only [productFraction, Equiv.symm_apply_apply]

theorem norm_productFraction_le (a : Fin ((m + 1) * (n + 1))) :
    ‖productFraction K A s t g h f k a‖ ≤ RationalIntersection.productRadii s t a := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
  have hl : ∀ i, ‖(Fin.cons 1 (leftFraction K A s t g h f k) : Fin (m + 1) → _) i‖ ≤
      (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) i :=
    Fin.cases (by simpa using norm_one_le K A s t g h f k)
      (fun i => by simpa using norm_leftFraction_le K A s t g h f k i)
  have hr : ∀ j, ‖(Fin.cons 1 (rightFraction K A s t g h f k) : Fin (n + 1) → _) j‖ ≤
      (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) j :=
    Fin.cases (by simpa using norm_one_le K A s t g h f k)
      (fun j => by simpa using norm_rightFraction_le K A s t g h f k j)
  rw [productFraction_pair, RationalIntersection.productRadii_pair]
  exact (norm_mul_le _ _).trans (mul_le_mul (hl i) (hr j) (norm_nonneg _)
    ((norm_nonneg _).trans (hl i)))

theorem productFraction_equation (a : Fin ((m + 1) * (n + 1))) :
    base K A s t g h f k (presentationMap K A (g * h)) * productFraction K A s t g h f k a =
      base K A s t g h f k (presentationMap K A (RationalIntersection.numerators K A g h f k a)) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
  have hl : ∀ i, base K A s t g h f k (presentationMap K A g) *
      (Fin.cons 1 (leftFraction K A s t g h f k) : Fin (m + 1) → _) i =
        base K A s t g h f k (presentationMap K A
          ((Fin.cons g f : Fin (m + 1) → _) i)) :=
    Fin.cases (by simp) (fun i => by simpa using leftFraction_equation K A s t g h f k i)
  have hr : ∀ j, base K A s t g h f k (presentationMap K A h) *
      (Fin.cons 1 (rightFraction K A s t g h f k) : Fin (n + 1) → _) j =
        base K A s t g h f k (presentationMap K A
          ((Fin.cons h k : Fin (n + 1) → _) j)) :=
    Fin.cases (by simp) (fun j => by simpa using rightFraction_equation K A s t g h f k j)
  rw [productFraction_pair, RationalIntersection.numerators_pair, map_mul, map_mul,
    map_mul, map_mul]
  calc
    _ = (base K A s t g h f k (presentationMap K A g) *
        (Fin.cons 1 (leftFraction K A s t g h f k) : Fin (m + 1) → _) i) *
      (base K A s t g h f k (presentationMap K A h) *
        (Fin.cons 1 (rightFraction K A s t g h f k) : Fin (n + 1) → _) j) := by ring
    _ = _ := by rw [hl, hr]

private theorem productFraction_monomial (d : Fin ((m + 1) * (n + 1)) →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A s t g h f k)
      (productFraction K A s t g h f k) d‖ ≤ (RationalIntersection.productRadii s t).weight d :=
  monomialValue_norm_le_weight (RationalIntersection.productRadii s t) (Algebra K A s t g h f k)
    (norm_one_le K A s t g h f k) (productFraction K A s t g h f k)
    (norm_productFraction_le K A s t g h f k) d

/-- The original right generation hypothesis remains true in the actual left quotient. -/
theorem generatesUnitIdeal_right (hk : GeneratesUnitIdeal K A h k) :
    RelativeRationalPresentation.GeneratesUnitIdeal K (algebra K A s g f)
      (baseMap K A s g f (presentationMap K A h))
      (fun j => baseMap K A s g f (presentationMap K A (k j))) := by
  let J : Ideal (algebra K A s g f) :=
    Ideal.span (insert (baseMap K A s g f (presentationMap K A h))
      (Set.range fun j => baseMap K A s g f (presentationMap K A (k j))))
  have hle : Ideal.span (insert (presentationMap K A h)
      (Set.range fun j => presentationMap K A (k j))) ≤
      Ideal.comap (baseMap K A s g f).toAlgHom.toRingHom J := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))
  have h1 : (1 : algebra K A s g f) ∈ J := by
    have hh := hle (show (1 : A) ∈ Ideal.span (insert (presentationMap K A h)
        (Set.range fun j => presentationMap K A (k j))) by
      rw [hk]
      trivial)
    simpa only [Ideal.mem_comap, map_one] using hh
  exact J.eq_top_iff_one.mpr h1

/-- Both original denominator images are units in the actual iterated quotient. -/
theorem isUnit_denominators (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k) :
    IsUnit (base K A s t g h f k (presentationMap K A g)) ∧
      IsUnit (base K A s t g h f k (presentationMap K A h)) := by
  refine ⟨(isUnit_baseMap_denominator K A s g f hf).map
    (coefficientMap K A s t g h f k).toAlgHom, ?_⟩
  let J : Ideal (Algebra K A s t g h f k) :=
    Ideal.span {base K A s t g h f k (presentationMap K A h)}
  have hle : Ideal.span (insert (baseMap K A s g f (presentationMap K A h))
      (Set.range fun j => baseMap K A s g f (presentationMap K A (k j)))) ≤
      Ideal.comap (coefficientMap K A s t g h f k).toAlgHom.toRingHom J := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact Ideal.mem_span_singleton_self _
    · change base K A s t g h f k (presentationMap K A (k j)) ∈ J
      exact Ideal.mem_span_singleton.mpr
        ⟨rightFraction K A s t g h f k j, (rightFraction_equation K A s t g h f k j).symm⟩
  have h1 : (1 : Algebra K A s t g h f k) ∈ J := by
    have hh := hle (show (1 : algebra K A s g f) ∈ Ideal.span
      (insert (baseMap K A s g f (presentationMap K A h))
        (Set.range fun j => baseMap K A s g f (presentationMap K A (k j)))) by
      rw [generatesUnitIdeal_right K A s g h f k hk]
      trivial)
    simpa only [Ideal.mem_comap, map_one] using hh
  exact Ideal.span_singleton_eq_top.mp (J.eq_top_iff_one.mpr h1)

variable [CompleteSpace K]
  (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k)

omit [CompleteSpace K] in
private theorem rightCoordinate_monomial (d : Fin n →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (RationalIntersection.Algebra K A s t g h f k)
      (RationalIntersection.rightCoordinate K A s t g h f k) d‖ ≤ t.weight d :=
  monomialValue_norm_le_weight t (RationalIntersection.Algebra K A s t g h f k)
    (PresentedAffinoidAlgebra.norm_one_le K (RationalIntersection.Algebra K A s t g h f k))
    (RationalIntersection.rightCoordinate K A s t g h f k)
    (RationalIntersection.norm_rightCoordinate_le K A s t g h f k) d

private theorem toProduct_equation (j : Fin n) :
    RationalIntersection.leftMap K A s t g h f k hf hk
        (baseMap K A s g f (presentationMap K A h)) *
      RationalIntersection.rightCoordinate K A s t g h f k j =
    RationalIntersection.leftMap K A s t g h f k hf hk
      (baseMap K A s g f (presentationMap K A (k j))) := by
  rw [RationalIntersection.leftMap_base, RationalIntersection.leftMap_base]
  exact RationalIntersection.rightCoordinate_equation K A s t g h f k hf hk j

/-- Evaluate the actual intrinsic quotient using the constructed left restriction
and the product quotient's right coordinates. -/
def toProduct : BoundedAlgHom K (Algebra K A s t g h f k)
    (RationalIntersection.Algebra K A s t g h f k) :=
  RelativeRationalPresentation.evaluate K (algebra K A s g f) t
    (baseMap K A s g f (presentationMap K A h))
    (fun j => baseMap K A s g f (presentationMap K A (k j)))
    (RationalIntersection.Algebra K A s t g h f k)
    (RationalIntersection.leftMap K A s t g h f k hf hk)
    (RationalIntersection.rightCoordinate K A s t g h f k)
    (RationalIntersection.norm_leftMap_le K A s t g h f k hf hk)
    (rightCoordinate_monomial K A s t g h f k)
    (toProduct_equation K A s t g h f k hf hk)

@[simp] theorem toProduct_coefficientMap (b : algebra K A s g f) :
    toProduct K A s t g h f k hf hk (coefficientMap K A s t g h f k b) =
      RationalIntersection.leftMap K A s t g h f k hf hk b := by
  simp only [toProduct, coefficientMap, RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem toProduct_base (a : A) :
    toProduct K A s t g h f k hf hk (base K A s t g h f k a) =
      RationalIntersection.base K A s t g h f k a := by
  change toProduct K A s t g h f k hf hk
    (coefficientMap K A s t g h f k (baseMap K A s g f a)) = _
  rw [toProduct_coefficientMap, RationalIntersection.leftMap_base]

@[simp] theorem toProduct_leftFraction (i : Fin m) :
    toProduct K A s t g h f k hf hk (leftFraction K A s t g h f k i) =
      RationalIntersection.leftCoordinate K A s t g h f k i := by
  rw [leftFraction, toProduct_coefficientMap, RationalIntersection.leftMap_fraction]

@[simp] theorem toProduct_rightFraction (j : Fin n) :
    toProduct K A s t g h f k hf hk (rightFraction K A s t g h f k j) =
      RationalIntersection.rightCoordinate K A s t g h f k j := by
  simp only [toProduct, rightFraction, RelativeRationalPresentation.evaluate_fraction]

theorem norm_toProduct_le (a : Algebra K A s t g h f k) :
    ‖toProduct K A s t g h f k hf hk a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le K (algebra K A s g f) t
    (baseMap K A s g f (presentationMap K A h))
    (fun j => baseMap K A s g f (presentationMap K A (k j)))
    (RationalIntersection.Algebra K A s t g h f k)
    (RationalIntersection.leftMap K A s t g h f k hf hk)
    (RationalIntersection.rightCoordinate K A s t g h f k)
    (RationalIntersection.norm_leftMap_le K A s t g h f k hf hk)
    (rightCoordinate_monomial K A s t g h f k)
    (toProduct_equation K A s t g h f k hf hk) a

/-- Cancel the unit product denominator to identify every product coordinate. -/
@[simp] theorem toProduct_productFraction (a : Fin ((m + 1) * (n + 1))) :
    toProduct K A s t g h f k hf hk (productFraction K A s t g h f k a) =
      fraction K A (RationalIntersection.productRadii s t) (g * h)
        (RationalIntersection.numerators K A g h f k) a := by
  have hu := isUnit_baseMap_denominator K A (RationalIntersection.productRadii s t) (g * h)
    (RationalIntersection.numerators K A g h f k)
    (RationalIntersection.generatesUnitIdeal K A g h f k hf hk)
  apply hu.mul_left_cancel
  have he := congrArg (toProduct K A s t g h f k hf hk)
    (productFraction_equation K A s t g h f k a)
  simp only [map_mul, toProduct_base] at he
  simpa only [RationalIntersection.base, map_mul] using he.trans
    (fraction_equation K A (RationalIntersection.productRadii s t) (g * h)
      (RationalIntersection.numerators K A g h f k) a).symm

/-- Evaluate all product coordinates at actual products of extended fractions.
Scalar-relative comparison keeps the original scalar quotient norm. -/
def fromProduct : BoundedAlgHom K (RationalIntersection.Algebra K A s t g h f k)
    (Algebra K A s t g h f k) :=
  (RelativeRationalPresentation.evaluate K A (RationalIntersection.productRadii s t)
    (presentationMap K A (g * h))
    (fun a => presentationMap K A (RationalIntersection.numerators K A g h f k a))
    (Algebra K A s t g h f k) (base K A s t g h f k) (productFraction K A s t g h f k)
    (norm_base_le K A s t g h f k) (productFraction_monomial K A s t g h f k)
    (productFraction_equation K A s t g h f k)).comp
      (relativeEquiv K A (RationalIntersection.productRadii s t) (g * h)
        (RationalIntersection.numerators K A g h f k)).toBoundedAlgHom

@[simp] theorem fromProduct_base (a : A) :
    fromProduct K A s t g h f k (RationalIntersection.base K A s t g h f k a) =
      base K A s t g h f k a := by
  simp only [fromProduct, RationalIntersection.base, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem fromProduct_fraction (a : Fin ((m + 1) * (n + 1))) :
    fromProduct K A s t g h f k
      (fraction K A (RationalIntersection.productRadii s t) (g * h)
        (RationalIntersection.numerators K A g h f k) a) = productFraction K A s t g h f k a := by
  simp only [fromProduct, BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    relativeEquiv_fraction, RelativeRationalPresentation.evaluate_fraction]

@[simp] theorem fromProduct_fractionCoordinate (i : Fin (m + 1)) (j : Fin (n + 1)) :
    fromProduct K A s t g h f k (RationalIntersection.fractionCoordinate K A s t g h f k i j) =
      (Fin.cons 1 (leftFraction K A s t g h f k) : Fin (m + 1) → _) i *
        (Fin.cons 1 (rightFraction K A s t g h f k) : Fin (n + 1) → _) j := by
  rw [RationalIntersection.fractionCoordinate, fromProduct_fraction, productFraction_pair]

@[simp] theorem fromProduct_leftCoordinate (i : Fin m) :
    fromProduct K A s t g h f k (RationalIntersection.leftCoordinate K A s t g h f k i) =
      leftFraction K A s t g h f k i := by
  simp only [RationalIntersection.leftCoordinate, fromProduct_fractionCoordinate,
    Fin.cons_succ, Fin.cons_zero, mul_one]

@[simp] theorem fromProduct_rightCoordinate (j : Fin n) :
    fromProduct K A s t g h f k (RationalIntersection.rightCoordinate K A s t g h f k j) =
      rightFraction K A s t g h f k j := by
  simp only [RationalIntersection.rightCoordinate, fromProduct_fractionCoordinate,
    Fin.cons_succ, Fin.cons_zero, one_mul]

theorem norm_fromProduct_le (a : RationalIntersection.Algebra K A s t g h f k) :
    ‖fromProduct K A s t g h f k a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A (RationalIntersection.productRadii s t)
    (presentationMap K A (g * h))
    (fun a => presentationMap K A (RationalIntersection.numerators K A g h f k a))
    (Algebra K A s t g h f k) (base K A s t g h f k) (productFraction K A s t g h f k)
    (norm_base_le K A s t g h f k) (productFraction_monomial K A s t g h f k)
    (productFraction_equation K A s t g h f k) _).trans_eq
      (norm_relativeEquiv K A (RationalIntersection.productRadii s t) (g * h)
        (RationalIntersection.numerators K A g h f k) a)

/-- Reverse evaluation recovers the whole actual coefficient map from B. -/
theorem fromProduct_comp_leftMap :
    (fromProduct K A s t g h f k).comp (RationalIntersection.leftMap K A s t g h f k hf hk) =
      coefficientMap K A s t g h f k := by
  apply hom_ext K A s g f (Algebra K A s t g h f k)
  · intro a
    change fromProduct K A s t g h f k
      (RationalIntersection.leftMap K A s t g h f k hf hk (baseMap K A s g f a)) = _
    rw [RationalIntersection.leftMap_base, fromProduct_base, coefficientMap_baseMap]
  · intro i
    change fromProduct K A s t g h f k
      (RationalIntersection.leftMap K A s t g h f k hf hk (fraction K A s g f i)) = _
    rw [RationalIntersection.leftMap_fraction, fromProduct_leftCoordinate]
    rfl

@[simp] theorem fromProduct_leftMap (b : algebra K A s g f) :
    fromProduct K A s t g h f k (RationalIntersection.leftMap K A s t g h f k hf hk b) =
      coefficientMap K A s t g h f k b :=
  congrArg (fun φ : BoundedAlgHom K (algebra K A s g f) (Algebra K A s t g h f k) => φ b)
    (fromProduct_comp_leftMap K A s t g h f k hf hk)

/-- The first inverse identity follows from intrinsic quotient extensionality. -/
theorem fromProduct_comp_toProduct :
    (fromProduct K A s t g h f k).comp (toProduct K A s t g h f k hf hk) =
      BoundedAlgHom.id K (Algebra K A s t g h f k) := by
  apply RelativeRationalPresentation.hom_ext K (algebra K A s g f) t
    (baseMap K A s g f (presentationMap K A h))
    (fun j => baseMap K A s g f (presentationMap K A (k j))) (Algebra K A s t g h f k)
  · intro b
    change fromProduct K A s t g h f k
      (toProduct K A s t g h f k hf hk (coefficientMap K A s t g h f k b)) =
        coefficientMap K A s t g h f k b
    rw [toProduct_coefficientMap, fromProduct_leftMap]
  · intro j
    change fromProduct K A s t g h f k
      (toProduct K A s t g h f k hf hk (rightFraction K A s t g h f k j)) =
        rightFraction K A s t g h f k j
    rw [toProduct_rightFraction, fromProduct_rightCoordinate]

/-- The second inverse identity uses scalar quotient extensionality and the
product-coordinate formulas proved by denominator cancellation. -/
theorem toProduct_comp_fromProduct :
    (toProduct K A s t g h f k hf hk).comp (fromProduct K A s t g h f k) =
      BoundedAlgHom.id K (RationalIntersection.Algebra K A s t g h f k) := by
  apply hom_ext K A (RationalIntersection.productRadii s t) (g * h)
    (RationalIntersection.numerators K A g h f k) (RationalIntersection.Algebra K A s t g h f k)
  · intro a
    change toProduct K A s t g h f k hf hk
      (fromProduct K A s t g h f k (RationalIntersection.base K A s t g h f k a)) = _
    rw [fromProduct_base, toProduct_base]
    rfl
  · intro a
    simp only [BoundedAlgHom.comp_apply, BoundedAlgHom.id_apply,
      fromProduct_fraction, toProduct_productFraction]

@[simp] theorem fromProduct_toProduct (a : Algebra K A s t g h f k) :
    fromProduct K A s t g h f k (toProduct K A s t g h f k hf hk a) = a :=
  congrArg (fun φ : BoundedAlgHom K (Algebra K A s t g h f k) (Algebra K A s t g h f k) => φ a)
    (fromProduct_comp_toProduct K A s t g h f k hf hk)

@[simp] theorem toProduct_fromProduct (a : RationalIntersection.Algebra K A s t g h f k) :
    toProduct K A s t g h f k hf hk (fromProduct K A s t g h f k a) = a :=
  congrArg (fun φ : BoundedAlgHom K (RationalIntersection.Algebra K A s t g h f k)
    (RationalIntersection.Algebra K A s t g h f k) => φ a)
    (toProduct_comp_fromProduct K A s t g h f k hf hk)

/-- The actual constructed bounded equivalence of iterated and product quotients. -/
def equiv : BoundedAlgEquiv K (Algebra K A s t g h f k)
    (RationalIntersection.Algebra K A s t g h f k) :=
  BoundedAlgEquiv.ofHomInv (toProduct K A s t g h f k hf hk) (fromProduct K A s t g h f k)
    (fromProduct_toProduct K A s t g h f k hf hk) (toProduct_fromProduct K A s t g h f k hf hk)

@[simp] theorem equiv_apply (a : Algebra K A s t g h f k) :
    equiv K A s t g h f k hf hk a = toProduct K A s t g h f k hf hk a := rfl

@[simp] theorem equiv_symm_apply (a : RationalIntersection.Algebra K A s t g h f k) :
    (equiv K A s t g h f k hf hk).symm a = fromProduct K A s t g h f k a := rfl

/-- Mutual contractivity proves equality of the two actual quotient norms. -/
theorem norm_equiv (a : Algebra K A s t g h f k) :
    ‖equiv K A s t g h f k hf hk a‖ = ‖a‖ := by
  apply le_antisymm (norm_toProduct_le K A s t g h f k hf hk a)
  simpa only [fromProduct_toProduct] using
    norm_fromProduct_le K A s t g h f k (toProduct K A s t g h f k hf hk a)

theorem norm_equiv_symm (a : RationalIntersection.Algebra K A s t g h f k) :
    ‖(equiv K A s t g h f k hf hk).symm a‖ = ‖a‖ := by
  have hh := norm_equiv K A s t g h f k hf hk ((equiv K A s t g h f k hf hk).symm a)
  rw [BoundedAlgEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem isometry_equiv : Isometry (equiv K A s t g h f k hf hk) :=
  AddMonoidHomClass.isometry_of_norm (equiv K A s t g h f k hf hk).toAlgEquiv
    (norm_equiv K A s t g h f k hf hk)

/-- The structural contravariant map to the spectrum of the actual coefficient algebra B. -/
def coefficientSpectrumMap : C(BanachSpectrum (Algebra K A s t g h f k),
    BanachSpectrum (algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (coefficientMap K A s t g h f k).toBoundedRingHom

/-- The structural contravariant map to the spectrum of the original algebra A. -/
def baseSpectrumMap : C(BanachSpectrum (Algebra K A s t g h f k), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (base K A s t g h f k).toBoundedRingHom

omit [CompleteSpace K] in
theorem baseSpectrumMap_eq_comp :
    baseSpectrumMap K A s t g h f k =
      (spectrumMap K A s g f).comp (coefficientSpectrumMap K A s t g h f k) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  rfl

/-- The actual spectrum homeomorphism, contravariant in the constructed equivalence. -/
def spectrumHomeomorph : BanachSpectrum (RationalIntersection.Algebra K A s t g h f k) ≃ₜ
    BanachSpectrum (Algebra K A s t g h f k) :=
  (equiv K A s t g h f k hf hk).spectrumHomeomorph

@[simp] theorem spectrumHomeomorph_apply
    (x : BanachSpectrum (RationalIntersection.Algebra K A s t g h f k))
    (a : Algebra K A s t g h f k) :
    spectrumHomeomorph K A s t g h f k hf hk x a =
      x (toProduct K A s t g h f k hf hk a) := rfl

@[simp] theorem spectrumHomeomorph_symm_apply
    (x : BanachSpectrum (Algebra K A s t g h f k))
    (a : RationalIntersection.Algebra K A s t g h f k) :
    (spectrumHomeomorph K A s t g h f k hf hk).symm x a =
      x (fromProduct K A s t g h f k a) := rfl

/-- Naturality to M(B) uses the whole constructed left restriction. -/
theorem spectrumHomeomorph_naturality_coefficient :
    (coefficientSpectrumMap K A s t g h f k).comp
      ⟨spectrumHomeomorph K A s t g h f k hf hk,
        (spectrumHomeomorph K A s t g h f k hf hk).continuous⟩ =
      RationalIntersection.leftSpectrumMap K A s t g h f k hf hk := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro b
  change x (toProduct K A s t g h f k hf hk (coefficientMap K A s t g h f k b)) = _
  rw [toProduct_coefficientMap]
  rfl

/-- Naturality to M(A) is equality of the actual structural continuous maps. -/
theorem spectrumHomeomorph_naturality_base :
    (baseSpectrumMap K A s t g h f k).comp
      ⟨spectrumHomeomorph K A s t g h f k hf hk,
        (spectrumHomeomorph K A s t g h f k hf hk).continuous⟩ =
      RationalIntersection.baseSpectrumMap K A s t g h f k := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (toProduct K A s t g h f k hf hk (base K A s t g h f k a)) = _
  rw [toProduct_base]
  rfl

theorem spectrumHomeomorph_symm_naturality_coefficient :
    (RationalIntersection.leftSpectrumMap K A s t g h f k hf hk).comp
      ⟨(spectrumHomeomorph K A s t g h f k hf hk).symm,
        (spectrumHomeomorph K A s t g h f k hf hk).symm.continuous⟩ =
      coefficientSpectrumMap K A s t g h f k := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro b
  change x (fromProduct K A s t g h f k
    (RationalIntersection.leftMap K A s t g h f k hf hk b)) = _
  rw [fromProduct_leftMap]
  rfl

theorem spectrumHomeomorph_symm_naturality_base :
    (RationalIntersection.baseSpectrumMap K A s t g h f k).comp
      ⟨(spectrumHomeomorph K A s t g h f k hf hk).symm,
        (spectrumHomeomorph K A s t g h f k hf hk).symm.continuous⟩ =
      baseSpectrumMap K A s t g h f k := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (fromProduct K A s t g h f k (RationalIntersection.base K A s t g h f k a)) = _
  rw [fromProduct_base]
  rfl

include hf hk in
/-- The exact published intersection range transfers to the actual iterated quotient. -/
theorem range_baseSpectrumMap :
    Set.range (baseSpectrumMap K A s t g h f k) = locus K A s g f ∩ locus K A t h k := by
  rw [← spectrumHomeomorph_symm_naturality_base K A s t g h f k hf hk]
  change Set.range ((RationalIntersection.baseSpectrumMap K A s t g h f k) ∘
    (spectrumHomeomorph K A s t g h f k hf hk).symm) = _
  rw [(spectrumHomeomorph K A s t g h f k hf hk).symm.surjective.range_comp]
  exact RationalIntersection.range_baseSpectrumMap K A s t g h f k hf hk

include hf hk in
/-- The actual iterated structural spectrum map is a closed embedding. -/
theorem isClosedEmbedding_baseSpectrumMap :
    Topology.IsClosedEmbedding (baseSpectrumMap K A s t g h f k) := by
  rw [← spectrumHomeomorph_symm_naturality_base K A s t g h f k hf hk]
  exact (RationalIntersection.isClosedEmbedding_baseSpectrumMap K A s t g h f k hf hk).comp
    (spectrumHomeomorph K A s t g h f k hf hk).symm.isClosedEmbedding

/-- The actual iterated spectrum identified with the two original rational loci. -/
def intersectionHomeomorph : BanachSpectrum (Algebra K A s t g h f k) ≃ₜ
    ↥(locus K A s g f ∩ locus K A t h k) :=
  (spectrumHomeomorph K A s t g h f k hf hk).symm.trans
    (RationalIntersection.intersectionHomeomorph K A s t g h f k hf hk)

@[simp] theorem intersectionHomeomorph_apply_coe
    (x : BanachSpectrum (Algebra K A s t g h f k)) :
    (intersectionHomeomorph K A s t g h f k hf hk x).val = baseSpectrumMap K A s t g h f k x := by
  exact congrArg (fun φ : C(BanachSpectrum (Algebra K A s t g h f k), BanachSpectrum A) => φ x)
    (spectrumHomeomorph_symm_naturality_base K A s t g h f k hf hk)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersectionIterated
