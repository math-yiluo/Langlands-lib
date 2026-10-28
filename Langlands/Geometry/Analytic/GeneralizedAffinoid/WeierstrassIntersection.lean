import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectrum

/-! # Combining two actual positive-radius Weierstrass quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.WeierstrassIntersection

open GeneralizedTateAlgebra

section ScalarEvaluation

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {k : ℕ} (r : PositivePolyradius (Fin k))
  (q : Fin k → GeneralizedTateAlgebra A.polyradius K)
  (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]
  (φ : BoundedAlgHom K A B) (b : Fin k → B)
  (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
  (hb : ∀ d : Fin k →₀ ℕ,
    ‖StrictTateAlgebra.monomialValue _ B b d‖ ≤ r.weight d)
  (hq : ∀ j, b j = φ (presentationMap K A (q j)))

private def scalarEvaluate : BoundedAlgHom K (weierstrassAlgebra K A r q) B :=
  (RelativeRationalPresentation.evaluate K A r (presentationMap K A 1)
    (fun j => presentationMap K A (q j)) B φ b hφ hb
    (fun j => by simpa only [map_one, one_mul] using hq j)).comp
      (relativeEquiv K A r 1 q).toBoundedAlgHom

@[simp] private theorem scalarEvaluate_base (a : A) :
    scalarEvaluate K A r q B φ b hφ hb hq (baseMap K A r 1 q a) = φ a := by
  simp only [scalarEvaluate, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]

@[simp] private theorem scalarEvaluate_fraction (j : Fin k) :
    scalarEvaluate K A r q B φ b hφ hb hq (fraction K A r 1 q j) = b j := by
  simp only [scalarEvaluate, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_fraction,
    RelativeRationalPresentation.evaluate_fraction]

private theorem norm_scalarEvaluate_le (a : weierstrassAlgebra K A r q) :
    ‖scalarEvaluate K A r q B φ b hφ hb hq a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A r (presentationMap K A 1)
    (fun j => presentationMap K A (q j)) B φ b hφ hb
    (fun j => by simpa only [map_one, one_mul] using hq j) _).trans_eq
      (norm_relativeEquiv K A r 1 q a)

end ScalarEvaluation

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m n : ℕ}
  (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (h : Fin n → GeneralizedTateAlgebra A.polyradius K)

/-- The scalar quotient imposing the first tuple of inequalities. -/
abbrev firstAlgebra : PresentedAffinoidAlgebra K := weierstrassAlgebra K A s f

/-- The second tuple, as actual elements of the first quotient. -/
def secondTuple (j : Fin n) : firstAlgebra K A s f :=
  baseMap K A s 1 f (presentationMap K A (h j))

/-- The actual relative Weierstrass quotient over the first quotient. -/
abbrev Algebra :=
  RelativeRationalPresentation.WeierstrassAlgebra K (firstAlgebra K A s f) t
    (secondTuple K A s f h)

/-- The single scalar quotient imposing the concatenated tuple. -/
abbrev combinedAlgebra : PresentedAffinoidAlgebra K :=
  weierstrassAlgebra K A (s.append t) (Fin.append f h)

/-- The coefficient map of the second quotient. -/
def iteratedBase : BoundedAlgHom K (firstAlgebra K A s f) (Algebra K A s t f h) :=
  RelativeRationalPresentation.baseMap K (firstAlgebra K A s f) t 1
    (secondTuple K A s f h)

/-- The composite structural map from the original coefficient algebra. -/
def base : BoundedAlgHom K A (Algebra K A s t f h) :=
  (iteratedBase K A s t f h).comp (baseMap K A s 1 f)

/-- The old coordinate, mapped into the second quotient. -/
def leftCoordinate (i : Fin m) : Algebra K A s t f h :=
  iteratedBase K A s t f h (fraction K A s 1 f i)

/-- The newly adjoined coordinate of the second quotient. -/
def rightCoordinate (j : Fin n) : Algebra K A s t f h :=
  RelativeRationalPresentation.fraction K (firstAlgebra K A s f) t 1
    (secondTuple K A s f h) j

theorem norm_iteratedBase_le (a : firstAlgebra K A s f) :
    ‖iteratedBase K A s t f h a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_baseMap_le K (firstAlgebra K A s f) t 1
    (secondTuple K A s f h) a

theorem norm_base_le (a : A) : ‖base K A s t f h a‖ ≤ ‖a‖ :=
  (norm_iteratedBase_le K A s t f h _).trans (norm_baseMap_le K A s 1 f a)

theorem leftCoordinate_eq_base (i : Fin m) :
    leftCoordinate K A s t f h i = base K A s t f h (presentationMap K A (f i)) := by
  change iteratedBase K A s t f h (fraction K A s 1 f i) = _
  rw [weierstrass_fraction]
  rfl

theorem rightCoordinate_eq_base (j : Fin n) :
    rightCoordinate K A s t f h j = base K A s t f h (presentationMap K A (h j)) :=
  RelativeRationalPresentation.weierstrass_fraction K (firstAlgebra K A s f) t
    (secondTuple K A s f h) j

theorem norm_leftCoordinate_le (i : Fin m) :
    ‖leftCoordinate K A s t f h i‖ ≤ s i :=
  (norm_iteratedBase_le K A s t f h _).trans (norm_fraction_le K A s 1 f i)

theorem norm_rightCoordinate_le (j : Fin n) :
    ‖rightCoordinate K A s t f h j‖ ≤ t j :=
  RelativeRationalPresentation.norm_fraction_le K (firstAlgebra K A s f) t 1
    (secondTuple K A s f h) j

/-- The combined inequalities are precisely the intersection in the original spectrum. -/
theorem combinedLocus_eq_inter :
    weierstrassLocus K A (s.append t) (Fin.append f h) =
      weierstrassLocus K A s f ∩ weierstrassLocus K A t h := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i => by simpa using hx (Fin.castAdd n i),
      fun j => by simpa using hx (Fin.natAdd m j)⟩
  · rintro ⟨hf, hh⟩ k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa using hf i
    · simpa using hh j

private def combinedTuple : Fin (m + n) → Algebra K A s t f h :=
  Fin.append (leftCoordinate K A s t f h) (rightCoordinate K A s t f h)

private theorem combinedTuple_norm (k : Fin (m + n)) :
    ‖combinedTuple K A s t f h k‖ ≤ (s.append t) k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedTuple, Fin.append_left, PositivePolyradius.append_castAdd] using
      norm_leftCoordinate_le K A s t f h i
  · simpa only [combinedTuple, Fin.append_right, PositivePolyradius.append_natAdd] using
      norm_rightCoordinate_le K A s t f h j

private theorem combinedTuple_equations (k : Fin (m + n)) :
    combinedTuple K A s t f h k =
      base K A s t f h (presentationMap K A (Fin.append f h k)) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedTuple, Fin.append_left] using leftCoordinate_eq_base K A s t f h i
  · simpa only [combinedTuple, Fin.append_right] using rightCoordinate_eq_base K A s t f h j

private theorem iterated_unit_norm : ‖(1 : Algebra K A s t f h)‖ ≤ 1 := by
  have h1 := norm_iteratedBase_le K A s t f h 1
  rw [map_one] at h1
  exact h1.trans (PresentedAffinoidAlgebra.norm_one_le K (firstAlgebra K A s f))

private theorem combinedTuple_monomial (d : Fin (m + n) →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A s t f h)
      (combinedTuple K A s t f h) d‖ ≤ (s.append t).weight d :=
  monomialValue_norm_le_weight (s.append t) (Algebra K A s t f h)
    (iterated_unit_norm K A s t f h) (combinedTuple K A s t f h)
    (combinedTuple_norm K A s t f h) d

/-- The left block coordinate in the combined quotient. -/
def combinedLeft (i : Fin m) : combinedAlgebra K A s t f h :=
  fraction K A (s.append t) 1 (Fin.append f h) (Fin.castAdd n i)

/-- The right block coordinate in the combined quotient. -/
def combinedRight (j : Fin n) : combinedAlgebra K A s t f h :=
  fraction K A (s.append t) 1 (Fin.append f h) (Fin.natAdd m j)

private theorem norm_combinedLeft (i : Fin m) :
    ‖combinedLeft K A s t f h i‖ ≤ s i := by
  simpa only [combinedLeft, PositivePolyradius.append_castAdd] using
    norm_fraction_le K A (s.append t) 1 (Fin.append f h) (Fin.castAdd n i)

private theorem norm_combinedRight (j : Fin n) :
    ‖combinedRight K A s t f h j‖ ≤ t j := by
  simpa only [combinedRight, PositivePolyradius.append_natAdd] using
    norm_fraction_le K A (s.append t) 1 (Fin.append f h) (Fin.natAdd m j)

private theorem combinedLeft_monomial (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (combinedAlgebra K A s t f h)
      (combinedLeft K A s t f h) d‖ ≤ s.weight d :=
  monomialValue_norm_le_weight s (combinedAlgebra K A s t f h)
    (PresentedAffinoidAlgebra.norm_one_le K (combinedAlgebra K A s t f h))
    (combinedLeft K A s t f h) (norm_combinedLeft K A s t f h) d

private theorem combinedRight_monomial (d : Fin n →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (combinedAlgebra K A s t f h)
      (combinedRight K A s t f h) d‖ ≤ t.weight d :=
  monomialValue_norm_le_weight t (combinedAlgebra K A s t f h)
    (PresentedAffinoidAlgebra.norm_one_le K (combinedAlgebra K A s t f h))
    (combinedRight K A s t f h) (norm_combinedRight K A s t f h) d

private theorem combinedLeft_equations (i : Fin m) :
    combinedLeft K A s t f h i =
      baseMap K A (s.append t) 1 (Fin.append f h) (presentationMap K A (f i)) := by
  simpa only [combinedLeft, Fin.append_left] using
    weierstrass_fraction K A (s.append t) (Fin.append f h) (Fin.castAdd n i)

private theorem combinedRight_equations (j : Fin n) :
    combinedRight K A s t f h j =
      baseMap K A (s.append t) 1 (Fin.append f h) (presentationMap K A (h j)) := by
  simpa only [combinedRight, Fin.append_right] using
    weierstrass_fraction K A (s.append t) (Fin.append f h) (Fin.natAdd m j)

variable [CompleteSpace K]

/-- Evaluate the single combined quotient in the actual iterated quotient. -/
def fromCombined : BoundedAlgHom K (combinedAlgebra K A s t f h) (Algebra K A s t f h) :=
  scalarEvaluate K A (s.append t) (Fin.append f h) (Algebra K A s t f h)
    (base K A s t f h) (combinedTuple K A s t f h)
    (norm_base_le K A s t f h) (combinedTuple_monomial K A s t f h)
    (combinedTuple_equations K A s t f h)

@[simp] theorem fromCombined_base (a : A) :
    fromCombined K A s t f h (baseMap K A (s.append t) 1 (Fin.append f h) a) =
      base K A s t f h a := scalarEvaluate_base _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem fromCombined_left (i : Fin m) :
    fromCombined K A s t f h (combinedLeft K A s t f h i) =
      leftCoordinate K A s t f h i := by
  simp only [fromCombined, combinedLeft, scalarEvaluate_fraction, combinedTuple, Fin.append_left]

@[simp] theorem fromCombined_right (j : Fin n) :
    fromCombined K A s t f h (combinedRight K A s t f h j) =
      rightCoordinate K A s t f h j := by
  simp only [fromCombined, combinedRight, scalarEvaluate_fraction, combinedTuple, Fin.append_right]

theorem norm_fromCombined_le (a : combinedAlgebra K A s t f h) :
    ‖fromCombined K A s t f h a‖ ≤ ‖a‖ :=
  norm_scalarEvaluate_le _ _ _ _ _ _ _ _ _ _ _

/-- The actual map from the first quotient to the combined quotient. -/
def firstMap : BoundedAlgHom K (firstAlgebra K A s f) (combinedAlgebra K A s t f h) :=
  scalarEvaluate K A s f (combinedAlgebra K A s t f h)
    (baseMap K A (s.append t) 1 (Fin.append f h)) (combinedLeft K A s t f h)
    (norm_baseMap_le K A (s.append t) 1 (Fin.append f h))
    (combinedLeft_monomial K A s t f h) (combinedLeft_equations K A s t f h)

@[simp] theorem firstMap_base (a : A) :
    firstMap K A s t f h (baseMap K A s 1 f a) =
      baseMap K A (s.append t) 1 (Fin.append f h) a :=
  scalarEvaluate_base _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem firstMap_fraction (i : Fin m) :
    firstMap K A s t f h (fraction K A s 1 f i) = combinedLeft K A s t f h i :=
  scalarEvaluate_fraction _ _ _ _ _ _ _ _ _ _ _

theorem norm_firstMap_le (a : firstAlgebra K A s f) :
    ‖firstMap K A s t f h a‖ ≤ ‖a‖ := norm_scalarEvaluate_le _ _ _ _ _ _ _ _ _ _ _

private theorem toCombined_equations (j : Fin n) :
    firstMap K A s t f h 1 * combinedRight K A s t f h j =
      firstMap K A s t f h (secondTuple K A s f h j) := by
  rw [map_one, one_mul, secondTuple, firstMap_base, combinedRight_equations]

/-- Evaluate the second quotient using the first quotient map and the right block. -/
def toCombined : BoundedAlgHom K (Algebra K A s t f h) (combinedAlgebra K A s t f h) :=
  RelativeRationalPresentation.evaluate K (firstAlgebra K A s f) t 1
    (secondTuple K A s f h) (combinedAlgebra K A s t f h)
    (firstMap K A s t f h) (combinedRight K A s t f h)
    (norm_firstMap_le K A s t f h) (combinedRight_monomial K A s t f h)
    (toCombined_equations K A s t f h)

@[simp] theorem toCombined_iteratedBase (a : firstAlgebra K A s f) :
    toCombined K A s t f h (iteratedBase K A s t f h a) = firstMap K A s t f h a :=
  RelativeRationalPresentation.evaluate_baseMap _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem toCombined_base (a : A) :
    toCombined K A s t f h (base K A s t f h a) =
      baseMap K A (s.append t) 1 (Fin.append f h) a := by
  change toCombined K A s t f h (iteratedBase K A s t f h (baseMap K A s 1 f a)) = _
  rw [toCombined_iteratedBase, firstMap_base]

@[simp] theorem toCombined_left (i : Fin m) :
    toCombined K A s t f h (leftCoordinate K A s t f h i) =
      combinedLeft K A s t f h i := by
  change toCombined K A s t f h (iteratedBase K A s t f h (fraction K A s 1 f i)) = _
  rw [toCombined_iteratedBase, firstMap_fraction]

@[simp] theorem toCombined_right (j : Fin n) :
    toCombined K A s t f h (rightCoordinate K A s t f h j) =
      combinedRight K A s t f h j :=
  RelativeRationalPresentation.evaluate_fraction _ _ _ _ _ _ _ _ _ _ _ _

theorem norm_toCombined_le (a : Algebra K A s t f h) :
    ‖toCombined K A s t f h a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le _ _ _ _ _ _ _ _ _ _ _ _

/-- The reverse evaluation extends the second quotient's coefficient map. -/
theorem fromCombined_comp_firstMap :
    (fromCombined K A s t f h).comp (firstMap K A s t f h) =
      iteratedBase K A s t f h := by
  apply hom_ext K A s 1 f (Algebra K A s t f h)
  · intro a
    change fromCombined K A s t f h
      (firstMap K A s t f h (baseMap K A s 1 f a)) =
        iteratedBase K A s t f h (baseMap K A s 1 f a)
    rw [firstMap_base, fromCombined_base]
    rfl
  · intro i
    change fromCombined K A s t f h (firstMap K A s t f h (fraction K A s 1 f i)) =
      leftCoordinate K A s t f h i
    rw [firstMap_fraction, fromCombined_left]

theorem fromCombined_toCombined (a : Algebra K A s t f h) :
    fromCombined K A s t f h (toCombined K A s t f h a) = a := by
  have heq : (fromCombined K A s t f h).comp (toCombined K A s t f h) =
      BoundedAlgHom.id K (Algebra K A s t f h) := by
    apply RelativeRationalPresentation.hom_ext K (firstAlgebra K A s f) t 1
      (secondTuple K A s f h) (Algebra K A s t f h)
    · intro b
      change fromCombined K A s t f h
        (toCombined K A s t f h (iteratedBase K A s t f h b)) =
          iteratedBase K A s t f h b
      rw [toCombined_iteratedBase]
      exact congrArg (fun ψ : BoundedAlgHom K (firstAlgebra K A s f)
        (Algebra K A s t f h) => ψ b) (fromCombined_comp_firstMap K A s t f h)
    · intro j
      change fromCombined K A s t f h
        (toCombined K A s t f h (rightCoordinate K A s t f h j)) =
          rightCoordinate K A s t f h j
      rw [toCombined_right, fromCombined_right]
  exact congrArg (fun ψ : BoundedAlgHom K (Algebra K A s t f h)
    (Algebra K A s t f h) => ψ a) heq

theorem toCombined_fromCombined (a : combinedAlgebra K A s t f h) :
    toCombined K A s t f h (fromCombined K A s t f h a) = a := by
  have heq : (toCombined K A s t f h).comp (fromCombined K A s t f h) =
      BoundedAlgHom.id K (combinedAlgebra K A s t f h) := by
    apply hom_ext K A (s.append t) 1 (Fin.append f h) (combinedAlgebra K A s t f h)
    · intro b
      change toCombined K A s t f h
        (fromCombined K A s t f h (baseMap K A (s.append t) 1 (Fin.append f h) b)) = _
      rw [fromCombined_base, toCombined_base]
      rfl
    · intro k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · change toCombined K A s t f h
          (fromCombined K A s t f h (combinedLeft K A s t f h i)) =
            combinedLeft K A s t f h i
        rw [fromCombined_left, toCombined_left]
      · change toCombined K A s t f h
          (fromCombined K A s t f h (combinedRight K A s t f h j)) =
            combinedRight K A s t f h j
        rw [fromCombined_right, toCombined_right]
  exact congrArg (fun ψ : BoundedAlgHom K (combinedAlgebra K A s t f h)
    (combinedAlgebra K A s t f h) => ψ a) heq

/-- Two successive actual Weierstrass quotients combine into one quotient
on the concatenated positive-radius tuple. Both inverses are constructed. -/
def equiv : BoundedAlgEquiv K (Algebra K A s t f h) (combinedAlgebra K A s t f h) :=
  BoundedAlgEquiv.ofHomInv (toCombined K A s t f h) (fromCombined K A s t f h)
    (fromCombined_toCombined K A s t f h) (toCombined_fromCombined K A s t f h)

@[simp] theorem equiv_iteratedBase (a : firstAlgebra K A s f) :
    equiv K A s t f h (iteratedBase K A s t f h a) = firstMap K A s t f h a :=
  toCombined_iteratedBase K A s t f h a

@[simp] theorem equiv_base (a : A) :
    equiv K A s t f h (base K A s t f h a) =
      baseMap K A (s.append t) 1 (Fin.append f h) a :=
  toCombined_base K A s t f h a

@[simp] theorem equiv_left (i : Fin m) :
    equiv K A s t f h (leftCoordinate K A s t f h i) = combinedLeft K A s t f h i :=
  toCombined_left K A s t f h i

@[simp] theorem equiv_right (j : Fin n) :
    equiv K A s t f h (rightCoordinate K A s t f h j) = combinedRight K A s t f h j :=
  toCombined_right K A s t f h j

/-- Both actual quotient norms agree, since the two constructed maps contract. -/
theorem norm_equiv (a : Algebra K A s t f h) :
    ‖equiv K A s t f h a‖ = ‖a‖ := by
  apply le_antisymm (norm_toCombined_le K A s t f h a)
  calc
    ‖a‖ = ‖fromCombined K A s t f h (toCombined K A s t f h a)‖ :=
      congrArg norm (fromCombined_toCombined K A s t f h a).symm
    _ ≤ ‖toCombined K A s t f h a‖ := norm_fromCombined_le K A s t f h _

theorem norm_equiv_symm (a : combinedAlgebra K A s t f h) :
    ‖(equiv K A s t f h).symm a‖ = ‖a‖ := by
  have heq := norm_equiv K A s t f h ((equiv K A s t f h).symm a)
  rw [BoundedAlgEquiv.apply_symm_apply] at heq
  exact heq.symm

theorem isometry_equiv : Isometry (equiv K A s t f h) :=
  AddMonoidHomClass.isometry_of_norm (equiv K A s t f h).toAlgEquiv
    (norm_equiv K A s t f h)

/-- The actual spectrum pullback of the second quotient's coefficient map. -/
def iteratedSpectrumMap :
    C(BanachSpectrum (Algebra K A s t f h), BanachSpectrum (firstAlgebra K A s f)) :=
  BanachSpectrum.comapContinuous (iteratedBase K A s t f h).toBoundedRingHom

/-- The combined quotient's spectrum map to the first quotient spectrum. -/
def firstSpectrumMap :
    C(BanachSpectrum (combinedAlgebra K A s t f h), BanachSpectrum (firstAlgebra K A s f)) :=
  BanachSpectrum.comapContinuous (firstMap K A s t f h).toBoundedRingHom

/-- The actual structural map to the original coefficient spectrum. -/
def baseSpectrumMap : C(BanachSpectrum (Algebra K A s t f h), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (base K A s t f h).toBoundedRingHom

/-- Contravariant spectrum homeomorphism induced by the constructed equivalence. -/
def spectrumHomeomorph :
    BanachSpectrum (combinedAlgebra K A s t f h) ≃ₜ BanachSpectrum (Algebra K A s t f h) :=
  (equiv K A s t f h).spectrumHomeomorph

@[simp] theorem spectrumHomeomorph_apply (x : BanachSpectrum (combinedAlgebra K A s t f h))
    (a : Algebra K A s t f h) :
    spectrumHomeomorph K A s t f h x a = x (equiv K A s t f h a) := rfl

/-- The homeomorphism respects the structural maps to the first quotient spectrum. -/
theorem spectrumHomeomorph_naturality :
    (iteratedSpectrumMap K A s t f h).comp
      ⟨spectrumHomeomorph K A s t f h, (spectrumHomeomorph K A s t f h).continuous⟩ =
        firstSpectrumMap K A s t f h := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (equiv K A s t f h (iteratedBase K A s t f h a)) = x (firstMap K A s t f h a)
  rw [equiv_iteratedBase]

@[simp] theorem baseSpectrumMap_homeomorph (x : BanachSpectrum (combinedAlgebra K A s t f h)) :
    baseSpectrumMap K A s t f h (spectrumHomeomorph K A s t f h x) =
      spectrumMap K A (s.append t) 1 (Fin.append f h) x := by
  apply BanachSpectrum.ext
  intro a
  change x (equiv K A s t f h (base K A s t f h a)) =
    x (baseMap K A (s.append t) 1 (Fin.append f h) a)
  rw [equiv_base]

@[simp] theorem spectrumMap_homeomorph_symm (x : BanachSpectrum (Algebra K A s t f h)) :
    spectrumMap K A (s.append t) 1 (Fin.append f h)
      ((spectrumHomeomorph K A s t f h).symm x) = baseSpectrumMap K A s t f h x := by
  have heq := baseSpectrumMap_homeomorph K A s t f h ((spectrumHomeomorph K A s t f h).symm x)
  rw [Homeomorph.apply_symm_apply] at heq
  exact heq.symm

omit [CompleteSpace K] in
private theorem combined_generates : GeneratesUnitIdeal K A 1 (Fin.append f h) := by
  apply (Ideal.span (insert (presentationMap K A 1)
    (Set.range fun j => presentationMap K A (Fin.append f h j)))).eq_top_iff_one.mpr
  apply Ideal.subset_span
  simp only [map_one, Set.mem_insert_iff, true_or]

/-- The iterated quotient has exactly the intersection of the two original
Weierstrass inequality loci as its structural spectrum image. -/
theorem range_baseSpectrumMap :
    Set.range (baseSpectrumMap K A s t f h) =
      weierstrassLocus K A s f ∩ weierstrassLocus K A t h := by
  have hr := range_spectrumMap K A (s.append t) 1 (Fin.append f h)
    (combined_generates K A f h)
  rw [locus_one, combinedLocus_eq_inter] at hr
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [← hr]
    exact ⟨(spectrumHomeomorph K A s t f h).symm y,
      spectrumMap_homeomorph_symm K A s t f h y⟩
  · intro hx
    have hx' : x ∈ Set.range (spectrumMap K A (s.append t) 1 (Fin.append f h)) := by
      rwa [hr]
    obtain ⟨y, hy⟩ := hx'
    exact ⟨spectrumHomeomorph K A s t f h y, (baseSpectrumMap_homeomorph K A s t f h y).trans hy⟩

theorem isClosedEmbedding_baseSpectrumMap :
    Topology.IsClosedEmbedding (baseSpectrumMap K A s t f h) := by
  apply (baseSpectrumMap K A s t f h).continuous.isClosedEmbedding
  intro x y hxy
  apply (spectrumHomeomorph K A s t f h).symm.injective
  apply spectrumMap_injective K A (s.append t) 1 (Fin.append f h) (combined_generates K A f h)
  rw [spectrumMap_homeomorph_symm, spectrumMap_homeomorph_symm, hxy]

/-- The spectrum of the actual iterated quotient, identified with the
intersection subspace by its structural map. -/
def intersectionHomeomorph :
    BanachSpectrum (Algebra K A s t f h) ≃ₜ
      ↥(weierstrassLocus K A s f ∩ weierstrassLocus K A t h) :=
  (isClosedEmbedding_baseSpectrumMap K A s t f h).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_baseSpectrumMap K A s t f h))

@[simp] theorem intersectionHomeomorph_apply_coe (x : BanachSpectrum (Algebra K A s t f h)) :
    (intersectionHomeomorph K A s t f h x).val = baseSpectrumMap K A s t f h x := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.WeierstrassIntersection
