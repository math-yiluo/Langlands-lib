import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRadiusRestriction

/-! # Radius decrease as an actual Weierstrass quotient -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RadiusWeierstrass

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s t : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- Adjoin variables of radii `t` to the actual quotient at `s`, equating
them to its existing fraction coordinates. -/
abbrev Algebra :=
  RelativeRationalPresentation.WeierstrassAlgebra K (algebra K A s g f) t
    (fraction K A s g f)

/-- The actual coefficient map into the relative Weierstrass quotient. -/
def base : BoundedAlgHom K (algebra K A s g f) (Algebra K A s t g f) :=
  RelativeRationalPresentation.baseMap K (algebra K A s g f) t 1 (fraction K A s g f)

/-- The newly adjoined coordinate in the Weierstrass quotient. -/
def coordinate (j : Fin m) : Algebra K A s t g f :=
  RelativeRationalPresentation.fraction K (algebra K A s g f) t 1
    (fraction K A s g f) j

theorem coordinate_eq_base (j : Fin m) :
    coordinate K A s t g f j = base K A s t g f (fraction K A s g f j) :=
  RelativeRationalPresentation.weierstrass_fraction K (algebra K A s g f) t
    (fraction K A s g f) j

theorem norm_base_le (a : algebra K A s g f) : ‖base K A s t g f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_baseMap_le K (algebra K A s g f) t 1
    (fraction K A s g f) a

theorem norm_coordinate_le (j : Fin m) : ‖coordinate K A s t g f j‖ ≤ t j :=
  RelativeRationalPresentation.norm_fraction_le K (algebra K A s g f) t 1
    (fraction K A s g f) j

private theorem unit_norm_le : ‖(1 : Algebra K A s t g f)‖ ≤ 1 := by
  have h := norm_base_le K A s t g f 1
  rw [map_one] at h
  exact h.trans (PresentedAffinoidAlgebra.norm_one_le K (algebra K A s g f))

private theorem coordinate_monomial_bound (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Algebra K A s t g f)
      (coordinate K A s t g f) d‖ ≤ t.weight d :=
  monomialValue_norm_le_weight t (Algebra K A s t g f)
    (unit_norm_le K A s t g f) (coordinate K A s t g f)
    (norm_coordinate_le K A s t g f) d

private def fromBase : BoundedAlgHom K A (Algebra K A s t g f) :=
  (base K A s t g f).comp (baseMap K A s g f)

private theorem norm_fromBase_le (a : A) : ‖fromBase K A s t g f a‖ ≤ ‖a‖ :=
  (norm_base_le K A s t g f _).trans (norm_baseMap_le K A s g f a)

private theorem fromEquations (j : Fin m) :
    fromBase K A s t g f (presentationMap K A g) * coordinate K A s t g f j =
      fromBase K A s t g f (presentationMap K A (f j)) := by
  change base K A s t g f (baseMap K A s g f (presentationMap K A g)) *
    coordinate K A s t g f j =
      base K A s t g f (baseMap K A s g f (presentationMap K A (f j)))
  rw [coordinate_eq_base, ← map_mul, fraction_equation]

variable [CompleteSpace K]

/-- Construct the map from the smaller scalar quotient to the actual
Weierstrass quotient by intrinsic bounded evaluation and scalar comparison.
This direction does not require an ordering of the radii. -/
def fromSmaller : BoundedAlgHom K (algebra K A t g f) (Algebra K A s t g f) :=
  (RelativeRationalPresentation.evaluate K A t (presentationMap K A g)
    (fun j => presentationMap K A (f j)) (Algebra K A s t g f)
    (fromBase K A s t g f) (coordinate K A s t g f)
    (norm_fromBase_le K A s t g f) (coordinate_monomial_bound K A s t g f)
    (fromEquations K A s t g f)).comp (relativeEquiv K A t g f).toBoundedAlgHom

@[simp] theorem fromSmaller_baseMap (a : A) :
    fromSmaller K A s t g f (baseMap K A t g f a) =
      base K A s t g f (baseMap K A s g f a) := by
  simp only [fromSmaller, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]
  rfl

@[simp] theorem fromSmaller_fraction (j : Fin m) :
    fromSmaller K A s t g f (fraction K A t g f j) = coordinate K A s t g f j := by
  simp only [fromSmaller, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply, relativeEquiv_fraction,
    RelativeRationalPresentation.evaluate_fraction]

theorem norm_fromSmaller_le (a : algebra K A t g f) :
    ‖fromSmaller K A s t g f a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A t (presentationMap K A g)
    (fun j => presentationMap K A (f j)) (Algebra K A s t g f)
    (fromBase K A s t g f) (coordinate K A s t g f)
    (norm_fromBase_le K A s t g f) (coordinate_monomial_bound K A s t g f)
    (fromEquations K A s t g f) _).trans_eq (norm_relativeEquiv K A t g f a)

omit [CompleteSpace K] in
private theorem smaller_monomial_bound (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (algebra K A t g f)
      (fraction K A t g f) d‖ ≤ t.weight d :=
  monomialValue_norm_le_weight t (algebra K A t g f)
    (PresentedAffinoidAlgebra.norm_one_le K (algebra K A t g f))
    (fraction K A t g f) (norm_fraction_le K A t g f) d

variable (hts : ∀ j, t j ≤ s j)

omit [CompleteSpace K] in
private theorem toEquations (j : Fin m) :
    radiusMap K A s t hts g f 1 * fraction K A t g f j =
      radiusMap K A s t hts g f (fraction K A s g f j) := by
  rw [map_one, one_mul, radiusMap_fraction]

/-- Evaluate the Weierstrass quotient in the smaller scalar quotient
using the actual contracting radius map and its fraction tuple. -/
def toSmaller : BoundedAlgHom K (Algebra K A s t g f) (algebra K A t g f) :=
  RelativeRationalPresentation.evaluate K (algebra K A s g f) t 1
    (fraction K A s g f) (algebra K A t g f) (radiusMap K A s t hts g f)
    (fraction K A t g f) (norm_radiusMap_le K A s t hts g f)
    (smaller_monomial_bound K A t g f) (toEquations K A s t g f hts)

@[simp] theorem toSmaller_base (a : algebra K A s g f) :
    toSmaller K A s t g f hts (base K A s t g f a) =
      radiusMap K A s t hts g f a := by
  simp only [toSmaller, base, RelativeRationalPresentation.evaluate_baseMap]

@[simp] theorem toSmaller_coordinate (j : Fin m) :
    toSmaller K A s t g f hts (coordinate K A s t g f j) =
      fraction K A t g f j := by
  simp only [toSmaller, coordinate, RelativeRationalPresentation.evaluate_fraction]

theorem norm_toSmaller_le (a : Algebra K A s t g f) :
    ‖toSmaller K A s t g f hts a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le K (algebra K A s g f) t 1
    (fraction K A s g f) (algebra K A t g f) (radiusMap K A s t hts g f)
    (fraction K A t g f) (norm_radiusMap_le K A s t hts g f)
    (smaller_monomial_bound K A t g f) (toEquations K A s t g f hts) a

/-- The constructed reverse map extends the Weierstrass coefficient map
along radius restriction. -/
theorem fromSmaller_comp_radiusMap :
    (fromSmaller K A s t g f).comp (radiusMap K A s t hts g f) =
      base K A s t g f := by
  apply hom_ext K A s g f (Algebra K A s t g f)
  · intro a
    change fromSmaller K A s t g f
      (radiusMap K A s t hts g f (baseMap K A s g f a)) =
        base K A s t g f (baseMap K A s g f a)
    rw [radiusMap_baseMap, fromSmaller_baseMap]
  · intro j
    change fromSmaller K A s t g f
      (radiusMap K A s t hts g f (fraction K A s g f j)) =
        base K A s t g f (fraction K A s g f j)
    rw [radiusMap_fraction, fromSmaller_fraction, coordinate_eq_base]

theorem fromSmaller_toSmaller (a : Algebra K A s t g f) :
    fromSmaller K A s t g f (toSmaller K A s t g f hts a) = a := by
  have h : (fromSmaller K A s t g f).comp (toSmaller K A s t g f hts) =
      BoundedAlgHom.id K (Algebra K A s t g f) := by
    apply RelativeRationalPresentation.hom_ext K (algebra K A s g f) t 1
      (fraction K A s g f) (Algebra K A s t g f)
    · intro b
      change fromSmaller K A s t g f
        (toSmaller K A s t g f hts (base K A s t g f b)) = base K A s t g f b
      rw [toSmaller_base]
      exact congrArg (fun φ : BoundedAlgHom K (algebra K A s g f)
        (Algebra K A s t g f) => φ b) (fromSmaller_comp_radiusMap K A s t g f hts)
    · intro j
      change fromSmaller K A s t g f
        (toSmaller K A s t g f hts (coordinate K A s t g f j)) =
          coordinate K A s t g f j
      rw [toSmaller_coordinate, fromSmaller_fraction]
  exact congrArg (fun φ : BoundedAlgHom K (Algebra K A s t g f)
    (Algebra K A s t g f) => φ a) h

theorem toSmaller_fromSmaller (a : algebra K A t g f) :
    toSmaller K A s t g f hts (fromSmaller K A s t g f a) = a := by
  have h : (toSmaller K A s t g f hts).comp (fromSmaller K A s t g f) =
      BoundedAlgHom.id K (algebra K A t g f) := by
    apply hom_ext K A t g f (algebra K A t g f)
    · intro b
      change toSmaller K A s t g f hts
        (fromSmaller K A s t g f (baseMap K A t g f b)) = baseMap K A t g f b
      rw [fromSmaller_baseMap, toSmaller_base, radiusMap_baseMap]
    · intro j
      change toSmaller K A s t g f hts
        (fromSmaller K A s t g f (fraction K A t g f j)) = fraction K A t g f j
      rw [fromSmaller_fraction, toSmaller_coordinate]
  exact congrArg (fun φ : BoundedAlgHom K (algebra K A t g f)
    (algebra K A t g f) => φ a) h

/-- Radius decrease is the actual relative Weierstrass quotient on
the existing fraction coordinates, with explicitly constructed bounded inverses. -/
def equiv : BoundedAlgEquiv K (Algebra K A s t g f) (algebra K A t g f) :=
  BoundedAlgEquiv.ofHomInv (toSmaller K A s t g f hts) (fromSmaller K A s t g f)
    (fromSmaller_toSmaller K A s t g f hts) (toSmaller_fromSmaller K A s t g f hts)

@[simp] theorem equiv_base (a : algebra K A s g f) :
    equiv K A s t g f hts (base K A s t g f a) = radiusMap K A s t hts g f a :=
  toSmaller_base K A s t g f hts a

@[simp] theorem equiv_coordinate (j : Fin m) :
    equiv K A s t g f hts (coordinate K A s t g f j) = fraction K A t g f j :=
  toSmaller_coordinate K A s t g f hts j

/-- The two constructed contractions imply equality of the actual quotient norms. -/
theorem norm_equiv (a : Algebra K A s t g f) :
    ‖equiv K A s t g f hts a‖ = ‖a‖ := by
  apply le_antisymm (norm_toSmaller_le K A s t g f hts a)
  calc
    ‖a‖ = ‖fromSmaller K A s t g f (toSmaller K A s t g f hts a)‖ :=
      congrArg norm (fromSmaller_toSmaller K A s t g f hts a).symm
    _ ≤ ‖toSmaller K A s t g f hts a‖ := norm_fromSmaller_le K A s t g f _

theorem norm_equiv_symm (a : algebra K A t g f) :
    ‖(equiv K A s t g f hts).symm a‖ = ‖a‖ := by
  have h := norm_equiv K A s t g f hts ((equiv K A s t g f hts).symm a)
  rw [BoundedAlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem isometry_equiv : Isometry (equiv K A s t g f hts) :=
  AddMonoidHomClass.isometry_of_norm (equiv K A s t g f hts).toAlgEquiv
    (norm_equiv K A s t g f hts)

/-- The actual continuous structural spectrum map of the Weierstrass quotient. -/
def spectrumMap :
    C(BanachSpectrum (Algebra K A s t g f), BanachSpectrum (algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (base K A s t g f).toBoundedRingHom

/-- The genuine spectrum homeomorphism induced by the constructed algebra equivalence. -/
def spectrumHomeomorph :
    BanachSpectrum (algebra K A t g f) ≃ₜ BanachSpectrum (Algebra K A s t g f) :=
  (equiv K A s t g f hts).spectrumHomeomorph

@[simp] theorem spectrumHomeomorph_apply (x : BanachSpectrum (algebra K A t g f))
    (a : Algebra K A s t g f) :
    spectrumHomeomorph K A s t g f hts x a = x (equiv K A s t g f hts a) := rfl

/-- Over the larger quotient spectrum, the Weierstrass structural map
becomes the original radius pullback. -/
theorem spectrumHomeomorph_naturality :
    (spectrumMap K A s t g f).comp
      ⟨spectrumHomeomorph K A s t g f hts,
        (spectrumHomeomorph K A s t g f hts).continuous⟩ =
      radiusSpectrumMap K A s t hts g f := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (equiv K A s t g f hts (base K A s t g f a)) =
    x (radiusMap K A s t hts g f a)
  rw [equiv_base]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RadiusWeierstrass
