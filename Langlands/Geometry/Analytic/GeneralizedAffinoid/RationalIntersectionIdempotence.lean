import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersection

/-! # Isometric idempotence of weighted rational intersections -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- The product of two entries in the denominator-extended fraction tuple. -/
def collapseTuple : Fin ((m + 1) * (m + 1)) → algebra K A s g f := fun a =>
  (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f)
      (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f)
      (finProdFinEquiv.symm a).2

@[simp] theorem collapseTuple_pair (i j : Fin (m + 1)) :
    collapseTuple K A s g f (finProdFinEquiv (i, j)) =
      (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) i *
        (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) j := by
  simp only [collapseTuple, Equiv.symm_apply_apply]

private theorem norm_extendedFraction_le (i : Fin (m + 1)) :
    ‖(Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) i‖ ≤
      (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) i := by
  induction i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using PresentedAffinoidAlgebra.norm_one_le K (algebra K A s g f)
  | succ i => simpa only [Fin.cons_succ] using norm_fraction_le K A s g f i

theorem norm_collapseTuple_le (a : Fin ((m + 1) * (m + 1))) :
    ‖collapseTuple K A s g f a‖ ≤ productRadii s s a := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
  rw [collapseTuple_pair, productRadii_pair]
  exact (norm_mul_le _ _).trans (mul_le_mul
    (norm_extendedFraction_le K A s g f i) (norm_extendedFraction_le K A s g f j)
    (norm_nonneg _) ((norm_nonneg _).trans (norm_extendedFraction_le K A s g f i)))

private theorem extendedFraction_equation (i : Fin (m + 1)) :
    baseMap K A s g f (presentationMap K A g) *
        (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) i =
      baseMap K A s g f (presentationMap K A
        ((Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K) i)) := by
  induction i using Fin.cases with
  | zero => simp only [Fin.cons_zero, mul_one]
  | succ i => simpa only [Fin.cons_succ] using fraction_equation K A s g f i

theorem collapseTuple_equation (a : Fin ((m + 1) * (m + 1))) :
    baseMap K A s g f (presentationMap K A (g * g)) * collapseTuple K A s g f a =
      baseMap K A s g f (presentationMap K A (numerators K A g g f f a)) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
  rw [collapseTuple_pair, numerators_pair]
  simp only [map_mul]
  calc
    _ = (baseMap K A s g f (presentationMap K A g) *
          (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) i) *
        (baseMap K A s g f (presentationMap K A g) *
          (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) j) := by ring
    _ = _ := by rw [extendedFraction_equation, extendedFraction_equation]

private theorem collapseTuple_monomial (d : Fin ((m + 1) * (m + 1)) →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (algebra K A s g f)
      (collapseTuple K A s g f) d‖ ≤ (productRadii s s).weight d :=
  monomialValue_norm_le_weight (productRadii s s) (algebra K A s g f)
    (PresentedAffinoidAlgebra.norm_one_le K (algebra K A s g f))
    (collapseTuple K A s g f) (norm_collapseTuple_le K A s g f) d

variable [CompleteSpace K]

/-- Evaluate product coordinates at products of actual fractions in one quotient. -/
def collapseMap : BoundedAlgHom K (Algebra K A s s g g f f) (algebra K A s g f) :=
  (RelativeRationalPresentation.evaluate K A (productRadii s s)
    (presentationMap K A (g * g)) (fun a => presentationMap K A (numerators K A g g f f a))
    (algebra K A s g f) (baseMap K A s g f) (collapseTuple K A s g f)
    (norm_baseMap_le K A s g f) (collapseTuple_monomial K A s g f)
    (collapseTuple_equation K A s g f)).comp
      (relativeEquiv K A (productRadii s s) (g * g) (numerators K A g g f f)).toBoundedAlgHom

@[simp] theorem collapseMap_base (a : A) :
    collapseMap K A s g f (base K A s s g g f f a) = baseMap K A s g f a := by
  simp only [collapseMap, base, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem collapseMap_fractionCoordinate (i j : Fin (m + 1)) :
    collapseMap K A s g f (fractionCoordinate K A s s g g f f i j) =
      (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) i *
        (Fin.cons 1 (fraction K A s g f) : Fin (m + 1) → algebra K A s g f) j := by
  simp only [collapseMap, fractionCoordinate, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_fraction,
    RelativeRationalPresentation.evaluate_fraction, collapseTuple_pair]

@[simp] theorem collapseMap_leftCoordinate (i : Fin m) :
    collapseMap K A s g f (leftCoordinate K A s s g g f f i) = fraction K A s g f i := by
  simp only [leftCoordinate, collapseMap_fractionCoordinate, Fin.cons_succ, Fin.cons_zero, mul_one]

@[simp] theorem collapseMap_rightCoordinate (i : Fin m) :
    collapseMap K A s g f (rightCoordinate K A s s g g f f i) = fraction K A s g f i := by
  simp only [rightCoordinate, collapseMap_fractionCoordinate, Fin.cons_succ, Fin.cons_zero, one_mul]

theorem norm_collapseMap_le (a : Algebra K A s s g g f f) :
    ‖collapseMap K A s g f a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A (productRadii s s)
    (presentationMap K A (g * g)) (fun a => presentationMap K A (numerators K A g g f f a))
    (algebra K A s g f) (baseMap K A s g f) (collapseTuple K A s g f)
    (norm_baseMap_le K A s g f) (collapseTuple_monomial K A s g f)
    (collapseTuple_equation K A s g f) _).trans_eq
      (norm_relativeEquiv K A (productRadii s s) (g * g) (numerators K A g g f f) a)

variable (hf : GeneratesUnitIdeal K A g f)

/-- The two restrictions to a repeated intersection agree as actual bounded maps. -/
theorem leftMap_eq_rightMap :
    leftMap K A s s g g f f hf hf = rightMap K A s s g g f f hf hf := by
  apply hom_ext_base K A s g f (Algebra K A s s g g f f) hf
  rw [leftMap_comp_baseMap, rightMap_comp_baseMap]

theorem collapseMap_comp_leftMap :
    (collapseMap K A s g f).comp (leftMap K A s s g g f f hf hf) =
      BoundedAlgHom.id K (algebra K A s g f) := by
  apply hom_ext_base K A s g f (algebra K A s g f) hf
  apply BoundedAlgHom.ext
  intro a
  change collapseMap K A s g f (leftMap K A s s g g f f hf hf (baseMap K A s g f a)) =
    baseMap K A s g f a
  rw [leftMap_base, collapseMap_base]

theorem leftMap_comp_collapseMap :
    (leftMap K A s s g g f f hf hf).comp (collapseMap K A s g f) =
      BoundedAlgHom.id K (Algebra K A s s g g f f) := by
  apply hom_ext_base K A (productRadii s s) (g * g) (numerators K A g g f f)
    (Algebra K A s s g g f f) (generatesUnitIdeal K A g g f f hf hf)
  apply BoundedAlgHom.ext
  intro a
  change leftMap K A s s g g f f hf hf (collapseMap K A s g f (base K A s s g g f f a)) =
    base K A s s g g f f a
  rw [collapseMap_base, leftMap_base]

@[simp] theorem leftMap_collapseMap (a : Algebra K A s s g g f f) :
    leftMap K A s s g g f f hf hf (collapseMap K A s g f a) = a :=
  congrArg (fun φ : BoundedAlgHom K (Algebra K A s s g g f f)
    (Algebra K A s s g g f f) => φ a) (leftMap_comp_collapseMap K A s g f hf)

@[simp] theorem collapseMap_leftMap (a : algebra K A s g f) :
    collapseMap K A s g f (leftMap K A s s g g f f hf hf a) = a :=
  congrArg (fun φ : BoundedAlgHom K (algebra K A s g f)
    (algebra K A s g f) => φ a) (collapseMap_comp_leftMap K A s g f hf)

/-- The constructed equivalence from the repeated product quotient to one quotient. -/
def idempotentEquiv : BoundedAlgEquiv K (Algebra K A s s g g f f) (algebra K A s g f) :=
  BoundedAlgEquiv.ofHomInv (collapseMap K A s g f) (leftMap K A s s g g f f hf hf)
    (leftMap_collapseMap K A s g f hf) (collapseMap_leftMap K A s g f hf)

@[simp] theorem idempotentEquiv_apply (a : Algebra K A s s g g f f) :
    idempotentEquiv K A s g f hf a = collapseMap K A s g f a := rfl

@[simp] theorem idempotentEquiv_symm_apply (a : algebra K A s g f) :
    (idempotentEquiv K A s g f hf).symm a = leftMap K A s s g g f f hf hf a := rfl

theorem norm_idempotentEquiv (a : Algebra K A s s g g f f) :
    ‖idempotentEquiv K A s g f hf a‖ = ‖a‖ := by
  apply le_antisymm (norm_collapseMap_le K A s g f a)
  have hle := norm_leftMap_le K A s s g g f f hf hf (collapseMap K A s g f a)
  rw [leftMap_collapseMap] at hle
  exact hle

theorem isometry_idempotentEquiv : Isometry (idempotentEquiv K A s g f hf) :=
  AddMonoidHomClass.isometry_of_norm (idempotentEquiv K A s g f hf).toAlgEquiv
    (norm_idempotentEquiv K A s g f hf)

theorem norm_idempotentEquiv_symm (a : algebra K A s g f) :
    ‖(idempotentEquiv K A s g f hf).symm a‖ = ‖a‖ := by
  have h := norm_idempotentEquiv K A s g f hf ((idempotentEquiv K A s g f hf).symm a)
  rw [BoundedAlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The actual contravariant spectrum homeomorphism identifying a repeated intersection. -/
def idempotentSpectrumHomeomorph :
    BanachSpectrum (algebra K A s g f) ≃ₜ BanachSpectrum (Algebra K A s s g g f f) :=
  (idempotentEquiv K A s g f hf).spectrumHomeomorph

@[simp] theorem idempotentSpectrumHomeomorph_apply
    (x : BanachSpectrum (algebra K A s g f)) (a : Algebra K A s s g g f f) :
    idempotentSpectrumHomeomorph K A s g f hf x a = x (collapseMap K A s g f a) := rfl

@[simp] theorem idempotentSpectrumHomeomorph_symm_apply
    (x : BanachSpectrum (Algebra K A s s g g f f)) (a : algebra K A s g f) :
    (idempotentSpectrumHomeomorph K A s g f hf).symm x a =
      x (leftMap K A s s g g f f hf hf a) := rfl

theorem idempotentSpectrumHomeomorph_naturality :
    (baseSpectrumMap K A s s g g f f).comp
        ⟨idempotentSpectrumHomeomorph K A s g f hf,
          (idempotentSpectrumHomeomorph K A s g f hf).continuous⟩ =
      spectrumMap K A s g f := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (collapseMap K A s g f (base K A s s g g f f a)) = x (baseMap K A s g f a)
  rw [collapseMap_base]

theorem leftSpectrumMap_idempotentSpectrumHomeomorph :
    (leftSpectrumMap K A s s g g f f hf hf).comp
        ⟨idempotentSpectrumHomeomorph K A s g f hf,
          (idempotentSpectrumHomeomorph K A s g f hf).continuous⟩ =
      ContinuousMap.id (BanachSpectrum (algebra K A s g f)) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (collapseMap K A s g f (leftMap K A s s g g f f hf hf a)) = x a
  rw [collapseMap_leftMap]

theorem rightSpectrumMap_idempotentSpectrumHomeomorph :
    (rightSpectrumMap K A s s g g f f hf hf).comp
        ⟨idempotentSpectrumHomeomorph K A s g f hf,
          (idempotentSpectrumHomeomorph K A s g f hf).continuous⟩ =
      ContinuousMap.id (BanachSpectrum (algebra K A s g f)) := by
  have h : rightSpectrumMap K A s s g g f f hf hf = leftSpectrumMap K A s s g g f f hf hf := by
    unfold rightSpectrumMap leftSpectrumMap
    rw [leftMap_eq_rightMap K A s g f hf]
  rw [h]
  exact leftSpectrumMap_idempotentSpectrumHomeomorph K A s g f hf

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection
