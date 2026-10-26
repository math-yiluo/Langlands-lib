import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Bounded transport through the relative-series comparison -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))

/-- Package the published mutually inverse bounded comparison maps. -/
def relativeSeriesEquiv :
    BoundedAlgEquiv K (algebra K A s ∅) (GeneralizedTateAlgebra s A) :=
  BoundedAlgEquiv.ofHomInv (relativeSeriesMap K A s) (relativeSeriesInverse K A s)
    (relativeSeriesInverse_map K A s) (relativeSeriesMap_inverse K A s)

@[simp] theorem relativeSeriesEquiv_apply (a : algebra K A s ∅) :
    relativeSeriesEquiv K A s a = relativeSeriesMap K A s a := rfl

@[simp] theorem relativeSeriesEquiv_symm_apply (f : GeneralizedTateAlgebra s A) :
    (relativeSeriesEquiv K A s).symm f = relativeSeriesInverse K A s f := rfl

/-- Reverse evaluation also preserves the actual norm exactly. -/
theorem norm_relativeSeriesInverse (f : GeneralizedTateAlgebra s A) :
    ‖relativeSeriesInverse K A s f‖ = ‖f‖ := by
  simpa only [relativeSeriesMap_inverse] using
    (norm_relativeSeriesMap K A s (relativeSeriesInverse K A s f)).symm

theorem isometry_relativeSeriesEquiv : Isometry (relativeSeriesEquiv K A s) :=
  isometry_relativeSeriesMap K A s

theorem isometry_relativeSeriesEquiv_symm : Isometry (relativeSeriesEquiv K A s).symm :=
  AddMonoidHomClass.isometry_of_norm (relativeSeriesInverse K A s).toAlgHom
    (norm_relativeSeriesInverse K A s)

variable {A} {B C : PresentedAffinoidAlgebra K}

/-- Transport a bounded base map to unconstrained adjunction of the same new variables. -/
def relativeSeriesTransport (φ : BoundedAlgHom K A B) :
    BoundedAlgHom K (algebra K A s ∅) (algebra K B s ∅) :=
  (relativeSeriesInverse K B s).comp
    ((mapCoefficientsAlgHom s φ).comp (relativeSeriesMap K A s))

@[simp] theorem relativeSeriesTransport_apply (φ : BoundedAlgHom K A B)
    (a : algebra K A s ∅) :
    relativeSeriesTransport K s φ a =
      relativeSeriesInverse K B s (mapCoefficientsAlgHom s φ (relativeSeriesMap K A s a)) :=
  rfl

/-- Under the comparison, transport is the actual coefficientwise map. -/
@[simp] theorem relativeSeriesMap_transport (φ : BoundedAlgHom K A B)
    (a : algebra K A s ∅) :
    relativeSeriesMap K B s (relativeSeriesTransport K s φ a) =
      mapCoefficientsAlgHom s φ (relativeSeriesMap K A s a) := by
  simp only [relativeSeriesTransport_apply, relativeSeriesMap_inverse]

/-- Every coefficient is mapped by the supplied base homomorphism. -/
theorem coeff_relativeSeriesMap_transport (φ : BoundedAlgHom K A B)
    (a : algebra K A s ∅) (d : Fin m →₀ ℕ) :
    MvPowerSeries.coeff d
        (series s B (relativeSeriesMap K B s (relativeSeriesTransport K s φ a))) =
      φ (MvPowerSeries.coeff d (series s A (relativeSeriesMap K A s a))) := by
  rw [relativeSeriesMap_transport, mapCoefficientsAlgHom_apply, coeff_mapCoefficients]
  rfl

@[simp] theorem relativeSeriesTransport_baseMap (φ : BoundedAlgHom K A B) (a : A) :
    relativeSeriesTransport K s φ (baseMap K A s ∅ a) = baseMap K B s ∅ (φ a) := by
  simp only [relativeSeriesTransport_apply, relativeSeriesMap_baseMap,
    mapCoefficientsAlgHom_apply, constantAlgHom_apply, mapCoefficients_algebraMap]
  exact relativeSeriesInverse_constant K B s (φ a)

@[simp] theorem relativeSeriesTransport_newCoordinate (φ : BoundedAlgHom K A B)
    (j : Fin m) :
    relativeSeriesTransport K s φ (newCoordinate K A s ∅ j) = newCoordinate K B s ∅ j := by
  simp only [relativeSeriesTransport_apply, relativeSeriesMap_newCoordinate,
    mapCoefficientsAlgHom_apply, mapCoefficients_X, relativeSeriesInverse_X]

/-- The induced maps respect identities on the actual enlarged quotients. -/
@[simp] theorem relativeSeriesTransport_id :
    relativeSeriesTransport K s (BoundedAlgHom.id K A) =
      BoundedAlgHom.id K (algebra K A s ∅) := by
  apply BoundedAlgHom.ext
  intro a
  simp only [relativeSeriesTransport_apply, mapCoefficientsAlgHom_id,
    BoundedAlgHom.id_apply, relativeSeriesInverse_map]

/-- The induced maps respect composition without choosing quotient representatives. -/
@[simp] theorem relativeSeriesTransport_comp
    (ψ : BoundedAlgHom K B C) (φ : BoundedAlgHom K A B) :
    relativeSeriesTransport K s (ψ.comp φ) =
      (relativeSeriesTransport K s ψ).comp (relativeSeriesTransport K s φ) := by
  apply BoundedAlgHom.ext
  intro a
  simp only [relativeSeriesTransport_apply, mapCoefficientsAlgHom_comp,
    BoundedAlgHom.comp_apply, relativeSeriesMap_inverse]

/-- Every supplied nonnegative operator bound transfers with the same constant. -/
theorem norm_relativeSeriesTransport_le (φ : BoundedAlgHom K A B) {c : ℝ}
    (hc : 0 ≤ c) (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖) (a : algebra K A s ∅) :
    ‖relativeSeriesTransport K s φ a‖ ≤ c * ‖a‖ := by
  rw [relativeSeriesTransport_apply, norm_relativeSeriesInverse]
  exact (norm_mapCoefficientsAlgHom_le s φ hc hφ (relativeSeriesMap K A s a)).trans_eq
    (congrArg (c * ·) (norm_relativeSeriesMap K A s a))

/-- An isometric base map induces a norm-preserving map of the enlarged quotients. -/
theorem norm_relativeSeriesTransport (φ : BoundedAlgHom K A B)
    (hφ : ∀ a, ‖φ a‖ = ‖a‖) (a : algebra K A s ∅) :
    ‖relativeSeriesTransport K s φ a‖ = ‖a‖ := by
  rw [relativeSeriesTransport_apply, norm_relativeSeriesInverse,
    mapCoefficientsAlgHom_apply, norm_mapCoefficients s φ.toBoundedRingHom hφ,
    norm_relativeSeriesMap]

theorem isometry_relativeSeriesTransport (φ : BoundedAlgHom K A B) (hφ : Isometry φ) :
    Isometry (relativeSeriesTransport K s φ) :=
  AddMonoidHomClass.isometry_of_norm (relativeSeriesTransport K s φ).toAlgHom
    (norm_relativeSeriesTransport K s φ
      (hφ.norm_map_of_map_zero (map_zero φ.toAlgHom)))

/-- A bounded equivalence of the base algebras induces an actual bounded equivalence
of their unconstrained variable-adjunction presentations. -/
def relativeSeriesTransportEquiv (e : BoundedAlgEquiv K A B) :
    BoundedAlgEquiv K (algebra K A s ∅) (algebra K B s ∅) :=
  BoundedAlgEquiv.ofHomInv
    (relativeSeriesTransport K s e.toBoundedAlgHom)
    (relativeSeriesTransport K s e.symm.toBoundedAlgHom)
    (fun a => by
      have h : e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom = BoundedAlgHom.id K A := by
        apply BoundedAlgHom.ext
        exact e.symm_apply_apply
      have h' := congrArg
        (fun φ : BoundedAlgHom K A A => relativeSeriesTransport K s φ a) h
      simpa only [relativeSeriesTransport_comp, relativeSeriesTransport_id,
        BoundedAlgHom.comp_apply, BoundedAlgHom.id_apply] using h')
    (fun b => by
      have h : e.toBoundedAlgHom.comp e.symm.toBoundedAlgHom = BoundedAlgHom.id K B := by
        apply BoundedAlgHom.ext
        exact e.apply_symm_apply
      have h' := congrArg
        (fun φ : BoundedAlgHom K B B => relativeSeriesTransport K s φ b) h
      simpa only [relativeSeriesTransport_comp, relativeSeriesTransport_id,
        BoundedAlgHom.comp_apply, BoundedAlgHom.id_apply] using h')

@[simp] theorem relativeSeriesTransportEquiv_apply (e : BoundedAlgEquiv K A B)
    (a : algebra K A s ∅) :
    relativeSeriesTransportEquiv K s e a = relativeSeriesTransport K s e.toBoundedAlgHom a :=
  rfl

@[simp] theorem relativeSeriesTransportEquiv_symm_apply (e : BoundedAlgEquiv K A B)
    (b : algebra K B s ∅) :
    (relativeSeriesTransportEquiv K s e).symm b =
      relativeSeriesTransport K s e.symm.toBoundedAlgHom b := rfl

/-- The forward bound of a base equivalence transfers unchanged. -/
theorem norm_relativeSeriesTransportEquiv_le (e : BoundedAlgEquiv K A B) {c : ℝ}
    (hc : 0 ≤ c) (he : ∀ a, ‖e a‖ ≤ c * ‖a‖) (a : algebra K A s ∅) :
    ‖relativeSeriesTransportEquiv K s e a‖ ≤ c * ‖a‖ :=
  norm_relativeSeriesTransport_le K s e.toBoundedAlgHom hc he a

/-- The inverse bound of a base equivalence also transfers unchanged. -/
theorem norm_relativeSeriesTransportEquiv_symm_le (e : BoundedAlgEquiv K A B) {c : ℝ}
    (hc : 0 ≤ c) (he : ∀ b, ‖e.symm b‖ ≤ c * ‖b‖) (b : algebra K B s ∅) :
    ‖(relativeSeriesTransportEquiv K s e).symm b‖ ≤ c * ‖b‖ :=
  norm_relativeSeriesTransport_le K s e.symm.toBoundedAlgHom hc he b

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
