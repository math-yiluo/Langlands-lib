import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRadiusRestriction

/-! # Coefficient and radius maps of intrinsic weighted rational quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  {A B C : PresentedAffinoidAlgebra K} {m : ℕ}
  (s : PositivePolyradius (Fin m)) (g : A) (f : Fin m → A)

/-- Coefficient maps send rational equations to rational equations with mapped data. -/
theorem mapCoefficients_equations (φ : BoundedAlgHom K A B) :
    Set.MapsTo (mapCoefficientsAlgHom s φ) (equations K A s g f)
      (equations K B s (φ g) (fun j => φ (f j))) := by
  rintro h ⟨j, rfl⟩
  refine ⟨j, ?_⟩
  symm
  change (mapCoefficientsAlgHom s φ).toAlgHom
    (constantAlgHom s K A g * X s A j - constantAlgHom s K A (f j)) = _
  rw [map_sub, map_mul]
  simp only [mapCoefficientsAlgHom_apply, constantAlgHom_apply,
    mapCoefficients_algebraMap, mapCoefficients_X]
  rfl

/-- The actual bounded map on rational quotients induced coefficientwise. -/
def transport (φ : BoundedAlgHom K A B) :
    BoundedAlgHom K (Algebra K A s g f)
      (Algebra K B s (φ g) (fun j => φ (f j))) :=
  RelativeRelations.transport K s (equations K A s g f)
    (equations K B s (φ g) (fun j => φ (f j))) φ
    (RelativeRelations.mapsRelations_of_mapsTo K s φ
      (mapCoefficients_equations K s g f φ))

@[simp] theorem transport_quotientMap (φ : BoundedAlgHom K A B)
    (h : GeneralizedTateAlgebra s A) :
    transport K s g f φ (quotientMap K A s g f h) =
      quotientMap K B s (φ g) (fun j => φ (f j)) (mapCoefficientsAlgHom s φ h) := rfl

@[simp] theorem transport_baseMap (φ : BoundedAlgHom K A B) (a : A) :
    transport K s g f φ (baseMap K A s g f a) =
      baseMap K B s (φ g) (fun j => φ (f j)) (φ a) :=
  RelativeRelations.transport_baseMap K s φ _ a

@[simp] theorem transport_fraction (φ : BoundedAlgHom K A B) (j : Fin m) :
    transport K s g f φ (fraction K A s g f j) =
      fraction K B s (φ g) (fun j => φ (f j)) j :=
  RelativeRelations.transport_newCoordinate K s φ _ j

/-- Every supplied nonnegative coefficient bound descends unchanged. -/
theorem norm_transport_le (φ : BoundedAlgHom K A B) {c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖) (a : Algebra K A s g f) :
    ‖transport K s g f φ a‖ ≤ c * ‖a‖ :=
  RelativeRelations.norm_transport_le K s φ _ hc hφ a

theorem norm_transport_le_of_contractive (φ : BoundedAlgHom K A B)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (a : Algebra K A s g f) :
    ‖transport K s g f φ a‖ ≤ ‖a‖ :=
  RelativeRelations.norm_transport_le_of_contractive K s φ _ hφ a

/-- Coefficient and fraction formulas characterize the transported map. -/
theorem eq_transport (φ : BoundedAlgHom K A B)
    (ψ : BoundedAlgHom K (Algebra K A s g f)
      (Algebra K B s (φ g) (fun j => φ (f j))))
    (hbase : ∀ a, ψ (baseMap K A s g f a) =
      baseMap K B s (φ g) (fun j => φ (f j)) (φ a))
    (hfrac : ∀ j, ψ (fraction K A s g f j) =
      fraction K B s (φ g) (fun j => φ (f j)) j) :
    ψ = transport K s g f φ := by
  apply hom_ext K A s g f _
  · intro a
    rw [transport_baseMap, hbase]
  · intro j
    rw [transport_fraction, hfrac]

@[simp] theorem transport_id :
    transport K s g f (BoundedAlgHom.id K A) =
      BoundedAlgHom.id K (Algebra K A s g f) :=
  RelativeRelations.transport_id K s (equations K A s g f)

theorem transport_comp (ψ : BoundedAlgHom K B C) (φ : BoundedAlgHom K A B) :
    transport K s g f (ψ.comp φ) =
      (transport K s (φ g) (fun j => φ (f j)) ψ).comp (transport K s g f φ) :=
  RelativeRelations.transport_comp K s ψ φ _ _

/-- Pullback on genuine quotient spectra, with the contravariant direction. -/
def spectrumTransport (φ : BoundedAlgHom K A B) :
    C(BanachSpectrum (Algebra K B s (φ g) (fun j => φ (f j))),
      BanachSpectrum (Algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (transport K s g f φ).toBoundedRingHom

@[simp] theorem spectrumTransport_apply (φ : BoundedAlgHom K A B)
    (x : BanachSpectrum (Algebra K B s (φ g) (fun j => φ (f j))))
    (a : Algebra K A s g f) :
    spectrumTransport K s g f φ x a = x (transport K s g f φ a) := rfl

/-- Coefficient-spectrum pullback sends the mapped rational inequalities to the originals. -/
def locusTransport (φ : BoundedAlgHom K A B) :
    C(locus K B s (φ g) (fun j => φ (f j)), locus K A s g f) where
  toFun x := ⟨BanachSpectrum.comap φ.toBoundedRingHom x.val, x.property⟩
  continuous_toFun :=
    ((BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem locusTransport_apply (φ : BoundedAlgHom K A B)
    (x : locus K B s (φ g) (fun j => φ (f j))) (a : A) :
    (locusTransport K s g f φ x).val a = x.val (φ a) := rfl

/-- The forward structural spectrum maps are natural in bounded coefficient maps. -/
theorem spectrumToLocus_transport (φ : BoundedAlgHom K A B) :
    (spectrumToLocus K A s g f).comp (spectrumTransport K s g f φ) =
      (locusTransport K s g f φ).comp
        (spectrumToLocus K B s (φ g) (fun j => φ (f j))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (transport_baseMap K s g f φ a)

section Radius

variable (t : PositivePolyradius (Fin m)) (hts : ∀ j, t j ≤ s j)

/-- Shrinking the radii leaves the actual rational equation expressions unchanged. -/
theorem restrictRadius_equations :
    Set.MapsTo (restrictRadiusAlgHom K s t hts A) (equations K A s g f)
      (equations K A t g f) := by
  rintro h ⟨j, rfl⟩
  refine ⟨j, ?_⟩
  symm
  change (restrictRadiusAlgHom K s t hts A).toAlgHom
    (constantAlgHom s K A g * X s A j - constantAlgHom s K A (f j)) = _
  rw [map_sub, map_mul]
  simp only [restrictRadiusAlgHom_constant, restrictRadiusAlgHom_X]

/-- Contractive radius restriction of the actual intrinsic rational quotients. -/
def radiusMap : BoundedAlgHom K (Algebra K A s g f) (Algebra K A t g f) :=
  RelativeRelations.radiusMap K A s t hts (equations K A s g f) (equations K A t g f)
    (RelativeRelations.radiusMapsRelations_of_mapsTo K A s t hts
      (restrictRadius_equations K s g f t hts))

@[simp] theorem radiusMap_quotientMap (h : GeneralizedTateAlgebra s A) :
    radiusMap K s g f t hts (quotientMap K A s g f h) =
      quotientMap K A t g f (restrictRadiusAlgHom K s t hts A h) := rfl

@[simp] theorem radiusMap_baseMap (a : A) :
    radiusMap K s g f t hts (baseMap K A s g f a) = baseMap K A t g f a :=
  RelativeRelations.radiusMap_baseMap K A s t hts _ a

@[simp] theorem radiusMap_fraction (j : Fin m) :
    radiusMap K s g f t hts (fraction K A s g f j) = fraction K A t g f j :=
  RelativeRelations.radiusMap_newCoordinate K A s t hts _ j

theorem norm_radiusMap_le (a : Algebra K A s g f) :
    ‖radiusMap K s g f t hts a‖ ≤ ‖a‖ :=
  RelativeRelations.norm_radiusMap_le K A s t hts _ a

/-- The restriction is determined by the coefficient and fraction formulas. -/
theorem eq_radiusMap (ψ : BoundedAlgHom K (Algebra K A s g f) (Algebra K A t g f))
    (hbase : ∀ a, ψ (baseMap K A s g f a) = baseMap K A t g f a)
    (hfrac : ∀ j, ψ (fraction K A s g f j) = fraction K A t g f j) :
    ψ = radiusMap K s g f t hts := by
  apply hom_ext K A s g f _
  · intro a
    rw [radiusMap_baseMap, hbase]
  · intro j
    rw [radiusMap_fraction, hfrac]

@[simp] theorem radiusMap_self :
    radiusMap K s g f s (fun _ => le_rfl) =
      BoundedAlgHom.id K (Algebra K A s g f) := by
  apply hom_ext K A s g f _
  · intro a
    simp only [radiusMap_baseMap, BoundedAlgHom.id_apply]
  · intro j
    simp only [radiusMap_fraction, BoundedAlgHom.id_apply]

theorem radiusMap_trans (q : PositivePolyradius (Fin m)) (hqt : ∀ j, q j ≤ t j) :
    (radiusMap K t g f q hqt).comp (radiusMap K s g f t hts) =
      radiusMap K s g f q (fun j => (hqt j).trans (hts j)) := by
  apply hom_ext K A s g f _
  · intro a
    simp only [BoundedAlgHom.comp_apply, radiusMap_baseMap]
  · intro j
    simp only [BoundedAlgHom.comp_apply, radiusMap_fraction]

/-- Coefficient transport and radius restriction commute on the actual quotients. -/
theorem radiusMap_transport (φ : BoundedAlgHom K A B) :
    (radiusMap K s (φ g) (fun j => φ (f j)) t hts).comp (transport K s g f φ) =
      (transport K t g f φ).comp (radiusMap K s g f t hts) := by
  apply hom_ext K A s g f _
  · intro a
    simp only [BoundedAlgHom.comp_apply, radiusMap_baseMap, transport_baseMap]
  · intro j
    simp only [BoundedAlgHom.comp_apply, radiusMap_fraction, transport_fraction]

/-- Contravariant pullback along rational radius restriction. -/
def radiusSpectrumMap :
    C(BanachSpectrum (Algebra K A t g f), BanachSpectrum (Algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (radiusMap K s g f t hts).toBoundedRingHom

@[simp] theorem radiusSpectrumMap_apply (x : BanachSpectrum (Algebra K A t g f))
    (a : Algebra K A s g f) :
    radiusSpectrumMap K s g f t hts x a = x (radiusMap K s g f t hts a) := rfl

/-- Rational inequalities at smaller radii imply the larger-radius inequalities. -/
def locusRadiusMap : C(locus K A t g f, locus K A s g f) where
  toFun x := ⟨x.val, fun j => (x.property j).trans
    (mul_le_mul_of_nonneg_right (hts j) (apply_nonneg x.val.toMulRingSeminorm g))⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem locusRadiusMap_apply (x : locus K A t g f) :
    (locusRadiusMap K s g f t hts x).val = x.val := rfl

theorem spectrumToLocus_radiusMap :
    (spectrumToLocus K A s g f).comp (radiusSpectrumMap K s g f t hts) =
      (locusRadiusMap K s g f t hts).comp (spectrumToLocus K A t g f) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (radiusMap_baseMap K s g f t hts a)

/-- The quotient-spectrum square commutes with the contravariant orientation. -/
theorem radiusSpectrumMap_spectrumTransport (φ : BoundedAlgHom K A B) :
    (spectrumTransport K s g f φ).comp
        (radiusSpectrumMap K s (φ g) (fun j => φ (f j)) t hts) =
      (radiusSpectrumMap K s g f t hts).comp (spectrumTransport K t g f φ) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (congrArg
    (fun ψ : BoundedAlgHom K (Algebra K A s g f)
      (Algebra K B t (φ g) (fun j => φ (f j))) => ψ a)
        (radiusMap_transport K s g f t hts φ))

/-- Coefficient pullback also commutes with the actual rational-locus inclusions. -/
theorem locusRadiusMap_locusTransport (φ : BoundedAlgHom K A B) :
    (locusTransport K s g f φ).comp (locusRadiusMap K s (φ g) (fun j => φ (f j)) t hts) =
      (locusRadiusMap K s g f t hts).comp (locusTransport K t g f φ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

end Radius

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation
