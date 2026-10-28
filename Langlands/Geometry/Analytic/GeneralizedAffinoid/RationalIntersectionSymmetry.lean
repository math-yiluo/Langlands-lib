import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersection

/-! # Isometric interchange of weighted rational intersection factors -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m n : ℕ}
  (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
  (g h : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (k : Fin n → GeneralizedTateAlgebra A.polyradius K)

/-- Transpose each actual product coordinate in the quotient with reversed factors. -/
def swapTuple : Fin ((m + 1) * (n + 1)) → Algebra K A t s h g k f := fun a =>
  fractionCoordinate K A t s h g k f
    (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm a).1

@[simp] theorem swapTuple_pair (i : Fin (m + 1)) (j : Fin (n + 1)) :
    swapTuple K A s t g h f k (finProdFinEquiv (i, j)) =
      fractionCoordinate K A t s h g k f j i := by
  simp only [swapTuple, Equiv.symm_apply_apply]

theorem norm_swapTuple_le (a : Fin ((m + 1) * (n + 1))) :
    ‖swapTuple K A s t g h f k a‖ ≤ productRadii s t a := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
  simpa only [swapTuple_pair, productRadii_pair, mul_comm] using
    norm_fractionCoordinate_le K A t s h g k f j i

theorem swapTuple_equation (a : Fin ((m + 1) * (n + 1))) :
    base K A t s h g k f (presentationMap K A (g * h)) * swapTuple K A s t g h f k a =
      base K A t s h g k f (presentationMap K A (numerators K A g h f k a)) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
  simpa only [swapTuple_pair, numerators_pair, mul_comm] using
    coordinate_equation K A t s h g k f j i

private theorem swapTuple_monomial (d : Fin ((m + 1) * (n + 1)) →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A t s h g k f)
      (swapTuple K A s t g h f k) d‖ ≤ (productRadii s t).weight d :=
  monomialValue_norm_le_weight (productRadii s t) (Algebra K A t s h g k f)
    (PresentedAffinoidAlgebra.norm_one_le K (Algebra K A t s h g k f))
    (swapTuple K A s t g h f k) (norm_swapTuple_le K A s t g h f k) d

variable [CompleteSpace K]

/-- Evaluate each product coordinate at its transpose to interchange the factors. -/
def swapMap : BoundedAlgHom K (Algebra K A s t g h f k) (Algebra K A t s h g k f) :=
  (RelativeRationalPresentation.evaluate K A (productRadii s t)
    (presentationMap K A (g * h)) (fun a => presentationMap K A (numerators K A g h f k a))
    (Algebra K A t s h g k f) (base K A t s h g k f) (swapTuple K A s t g h f k)
    (norm_base_le K A t s h g k f) (swapTuple_monomial K A s t g h f k)
    (swapTuple_equation K A s t g h f k)).comp
      (relativeEquiv K A (productRadii s t) (g * h) (numerators K A g h f k)).toBoundedAlgHom

@[simp] theorem swapMap_base (a : A) :
    swapMap K A s t g h f k (base K A s t g h f k a) = base K A t s h g k f a := by
  simp only [swapMap, base, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem swapMap_fractionCoordinate (i : Fin (m + 1)) (j : Fin (n + 1)) :
    swapMap K A s t g h f k (fractionCoordinate K A s t g h f k i j) =
      fractionCoordinate K A t s h g k f j i := by
  simp only [swapMap, fractionCoordinate, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_fraction,
    RelativeRationalPresentation.evaluate_fraction, swapTuple_pair]

theorem norm_swapMap_le (a : Algebra K A s t g h f k) :
    ‖swapMap K A s t g h f k a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A (productRadii s t)
    (presentationMap K A (g * h)) (fun a => presentationMap K A (numerators K A g h f k a))
    (Algebra K A t s h g k f) (base K A t s h g k f) (swapTuple K A s t g h f k)
    (norm_base_le K A t s h g k f) (swapTuple_monomial K A s t g h f k)
    (swapTuple_equation K A s t g h f k) _).trans_eq
      (norm_relativeEquiv K A (productRadii s t) (g * h) (numerators K A g h f k) a)

/-- Interchanging the factors twice fixes the actual quotient, including its coefficients. -/
theorem swapMap_comp_swapMap :
    (swapMap K A t s h g k f).comp (swapMap K A s t g h f k) =
      BoundedAlgHom.id K (Algebra K A s t g h f k) := by
  apply hom_ext K A (productRadii s t) (g * h) (numerators K A g h f k) _
  · intro a
    change swapMap K A t s h g k f
      (swapMap K A s t g h f k (base K A s t g h f k a)) = base K A s t g h f k a
    rw [swapMap_base, swapMap_base]
  · intro a
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
    change swapMap K A t s h g k f
      (swapMap K A s t g h f k (fractionCoordinate K A s t g h f k i j)) =
        fractionCoordinate K A s t g h f k i j
    rw [swapMap_fractionCoordinate, swapMap_fractionCoordinate]

@[simp] theorem swapMap_involutive (a : Algebra K A s t g h f k) :
    swapMap K A t s h g k f (swapMap K A s t g h f k a) = a :=
  congrArg (fun φ : BoundedAlgHom K (Algebra K A s t g h f k)
    (Algebra K A s t g h f k) => φ a) (swapMap_comp_swapMap K A s t g h f k)

/-- The constructed bounded equivalence that reverses the two weighted rational factors. -/
def swapEquiv : BoundedAlgEquiv K (Algebra K A s t g h f k) (Algebra K A t s h g k f) :=
  BoundedAlgEquiv.ofHomInv (swapMap K A s t g h f k) (swapMap K A t s h g k f)
    (swapMap_involutive K A s t g h f k) (swapMap_involutive K A t s h g k f)

@[simp] theorem swapEquiv_apply (a : Algebra K A s t g h f k) :
    swapEquiv K A s t g h f k a = swapMap K A s t g h f k a := rfl

theorem norm_swapEquiv (a : Algebra K A s t g h f k) :
    ‖swapEquiv K A s t g h f k a‖ = ‖a‖ := by
  apply le_antisymm (norm_swapMap_le K A s t g h f k a)
  have hle := norm_swapMap_le K A t s h g k f (swapMap K A s t g h f k a)
  rw [swapMap_involutive] at hle
  exact hle

theorem isometry_swapEquiv : Isometry (swapEquiv K A s t g h f k) :=
  AddMonoidHomClass.isometry_of_norm (swapEquiv K A s t g h f k).toAlgEquiv
    (norm_swapEquiv K A s t g h f k)

@[simp] theorem swapEquiv_symm_apply (a : Algebra K A t s h g k f) :
    (swapEquiv K A s t g h f k).symm a = swapMap K A t s h g k f a := rfl

theorem norm_swapEquiv_symm (a : Algebra K A t s h g k f) :
    ‖(swapEquiv K A s t g h f k).symm a‖ = ‖a‖ :=
  norm_swapEquiv K A t s h g k f a

theorem swapMap_comp_base :
    (swapMap K A s t g h f k).comp (base K A s t g h f k) = base K A t s h g k f := by
  apply BoundedAlgHom.ext
  exact swapMap_base K A s t g h f k

/-- The actual contravariant spectrum homeomorphism of the reversed product quotients. -/
def swapSpectrumHomeomorph :
    BanachSpectrum (Algebra K A t s h g k f) ≃ₜ BanachSpectrum (Algebra K A s t g h f k) :=
  (swapEquiv K A s t g h f k).spectrumHomeomorph

@[simp] theorem swapSpectrumHomeomorph_apply
    (x : BanachSpectrum (Algebra K A t s h g k f)) (a : Algebra K A s t g h f k) :
    swapSpectrumHomeomorph K A s t g h f k x a = x (swapMap K A s t g h f k a) := rfl

@[simp] theorem swapSpectrumHomeomorph_symm_apply
    (x : BanachSpectrum (Algebra K A s t g h f k)) (a : Algebra K A t s h g k f) :
    (swapSpectrumHomeomorph K A s t g h f k).symm x a = x (swapMap K A t s h g k f a) := rfl

/-- Swapping factors fixes the structural spectrum map to the original coefficient algebra. -/
theorem swapSpectrumHomeomorph_naturality :
    (baseSpectrumMap K A s t g h f k).comp
        ⟨swapSpectrumHomeomorph K A s t g h f k,
          (swapSpectrumHomeomorph K A s t g h f k).continuous⟩ =
      baseSpectrumMap K A t s h g k f := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (swapMap K A s t g h f k (base K A s t g h f k a)) =
    x (base K A t s h g k f a)
  rw [swapMap_base]

variable (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k)

/-- The constructed swap exchanges the left restriction with the reversed right restriction. -/
theorem swapMap_comp_leftMap :
    (swapMap K A s t g h f k).comp (leftMap K A s t g h f k hf hk) =
      rightMap K A t s h g k f hk hf := by
  apply hom_ext K A s g f _
  · intro a
    simp only [BoundedAlgHom.comp_apply, leftMap_base, rightMap_base, swapMap_base]
  · intro i
    simp only [BoundedAlgHom.comp_apply, leftMap_fraction, rightMap_fraction]
    exact swapMap_fractionCoordinate K A s t g h f k i.succ 0

/-- The constructed swap exchanges the right restriction with the reversed left restriction. -/
theorem swapMap_comp_rightMap :
    (swapMap K A s t g h f k).comp (rightMap K A s t g h f k hf hk) =
      leftMap K A t s h g k f hk hf := by
  apply hom_ext K A t h k _
  · intro a
    simp only [BoundedAlgHom.comp_apply, rightMap_base, leftMap_base, swapMap_base]
  · intro j
    simp only [BoundedAlgHom.comp_apply, rightMap_fraction, leftMap_fraction]
    exact swapMap_fractionCoordinate K A s t g h f k 0 j.succ

/-- Contravariant spectrum pullback exchanges the two restriction maps. -/
theorem leftSpectrumMap_swapSpectrumHomeomorph :
    (leftSpectrumMap K A s t g h f k hf hk).comp
        ⟨swapSpectrumHomeomorph K A s t g h f k,
          (swapSpectrumHomeomorph K A s t g h f k).continuous⟩ =
      rightSpectrumMap K A t s h g k f hk hf := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro b
  change x (swapMap K A s t g h f k (leftMap K A s t g h f k hf hk b)) =
    x (rightMap K A t s h g k f hk hf b)
  exact congrArg x (congrArg (fun φ : BoundedAlgHom K (algebra K A s g f)
    (Algebra K A t s h g k f) => φ b) (swapMap_comp_leftMap K A s t g h f k hf hk))

theorem rightSpectrumMap_swapSpectrumHomeomorph :
    (rightSpectrumMap K A s t g h f k hf hk).comp
        ⟨swapSpectrumHomeomorph K A s t g h f k,
          (swapSpectrumHomeomorph K A s t g h f k).continuous⟩ =
      leftSpectrumMap K A t s h g k f hk hf := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro c
  change x (swapMap K A s t g h f k (rightMap K A s t g h f k hf hk c)) =
    x (leftMap K A t s h g k f hk hf c)
  exact congrArg x (congrArg (fun φ : BoundedAlgHom K (algebra K A t h k)
    (Algebra K A t s h g k f) => φ c) (swapMap_comp_rightMap K A s t g h f k hf hk))

/-- Both identifications of the intersection have the same actual underlying point of M(A). -/
theorem intersectionHomeomorph_swapSpectrumHomeomorph
    (x : BanachSpectrum (Algebra K A t s h g k f)) :
    (intersectionHomeomorph K A s t g h f k hf hk
      (swapSpectrumHomeomorph K A s t g h f k x)).val =
        (intersectionHomeomorph K A t s h g k f hk hf x).val := by
  apply BanachSpectrum.ext
  intro a
  change x (swapMap K A s t g h f k (base K A s t g h f k a)) =
    x (base K A t s h g k f a)
  rw [swapMap_base]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection
