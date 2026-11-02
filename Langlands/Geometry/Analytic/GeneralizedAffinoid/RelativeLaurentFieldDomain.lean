import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidScalarRestriction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentScalarExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentDomain

/-! # Full domain representations over an independent Laurent coefficient field -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace PresentedAffinoidAlgebra.ScalarRestriction

/-- Preserve the bound while restricting a compatible scalar action. -/
def restrictHom (K : Type u) {L : Type u} {E : Type v} {F : Type w}
    [NormedField K] [NormedField L] [NormedCommRing E] [NormedCommRing F]
    [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L E] [Algebra L F]
    [IsScalarTower K L E] [IsScalarTower K L F]
    (φ : BoundedAlgHom L E F) : BoundedAlgHom K E F where
  toAlgHom := φ.toAlgHom.restrictScalars K
  bounded := φ.bounded

variable (K L : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (S : PresentedAffinoidAlgebra K) (e : BoundedAlgEquiv K S L)
  (he : ∀ a, ‖e a‖ = ‖a‖)
  (A B : PresentedAffinoidAlgebra K)
  [NormedAlgebra L A] [NormedAlgebra L B]
  [IsScalarTower K L A] [IsScalarTower K L B]
  (i : BoundedAlgHom L A B) (U : Set (BanachSpectrum A))

include he in
/-- Full representation over the original field tests every affinoid over the
extension field when that field has an isometric affinoid presentation. -/
theorem existsUnique_factor_over_extension
    (hi : Represents K (restrictHom K i) U)
    (R : PresentedAffinoidAlgebra L) (α : BoundedAlgHom L A R)
    (hα : ∀ x : BanachSpectrum R, BanachSpectrum.comap α.toBoundedRingHom x ∈ U) :
    ∃! β : BoundedAlgHom L B R, β.comp i = α := by
  letI : NormedAlgebra K R := NormedAlgebra.restrictScalars K L R
  letI : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq' rfl
  let R₀ := presentation K L S e R
  let E := boundedEquiv K L S e he R
  let α₀ := E.symm.toBoundedAlgHom.comp (restrictHom K α)
  have hα₀ : HasImageIn K α₀ U := by
    intro x
    exact hα (BanachSpectrum.comap E.symm.toBoundedAlgHom.toBoundedRingHom x)
  obtain ⟨β₀, hβ₀, huniq⟩ := hi.2.2 R₀ α₀ hα₀
  let βR := E.toBoundedAlgHom.comp β₀
  have hβR (a : A) : βR (i a) = α a := by
    have h := congrArg (fun φ : BoundedAlgHom K A R₀ => E (φ a)) hβ₀
    exact h.trans (E.apply_symm_apply (α a))
  let β : BoundedAlgHom L B R :=
    { toAlgHom :=
        { toRingHom := βR.toAlgHom.toRingHom
          commutes' := fun z => by
            calc
              βR (algebraMap L B z) = βR (i (algebraMap L A z)) :=
                congrArg βR (i.toAlgHom.commutes z).symm
              _ = α (algebraMap L A z) := hβR _
              _ = algebraMap L R z := α.toAlgHom.commutes z }
      bounded := βR.bounded }
  refine ⟨β, BoundedAlgHom.ext hβR, ?_⟩
  intro θ hθ
  let θ₀ := E.symm.toBoundedAlgHom.comp (restrictHom K θ)
  have hθ₀ : θ₀.comp (restrictHom K i) = α₀ := by
    apply BoundedAlgHom.ext
    intro a
    exact congrArg E.symm
      (congrArg (fun φ : BoundedAlgHom L A R => φ a) hθ)
  have h := huniq θ₀ hθ₀
  apply BoundedAlgHom.ext
  intro b
  have hb := congrArg (fun φ : BoundedAlgHom K B R₀ => E (φ b)) h
  exact (E.apply_symm_apply (θ b)).symm.trans hb

end PresentedAffinoidAlgebra.ScalarRestriction

namespace RelativeLaurentAnnulus.ScalarExtension

open PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : ℝ) [Fact (0 < t)]
  [H : Fact (∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)]
  {A B : PresentedAffinoidAlgebra K}

/-- Actual annulus transport preserves the completed coefficient field. -/
def transportOverExtension (φ : BoundedAlgHom K A B) :
    BoundedAlgHom (CompletedGaussLaurent K t) (algebra K A t) (algebra K B t) where
  toAlgHom :=
    { toRingHom := (transport K t φ).toAlgHom.toRingHom
      commutes' := fun z => congrArg
        (fun χ : BoundedAlgHom K (CompletedGaussLaurent K t) (algebra K B t) => χ z)
        (transport_completedScalarMap K A t φ) }
  bounded := (transport K t φ).bounded

/-- The structural map between actual coefficient-extended presentations. -/
def fieldMap (φ : BoundedAlgHom K A B) :
    BoundedAlgHom (CompletedGaussLaurent K t) (presentation K A t) (presentation K B t) :=
  (toPresentationOverExtension K B t).comp
    ((transportOverExtension K t φ).comp (fromPresentationOverExtension K A t))

theorem fieldMap_spectrum (φ : BoundedAlgHom K A B)
    (y : BanachSpectrum (presentation K B t)) :
    (boundedEquiv K A t).spectrumHomeomorph
        (BanachSpectrum.comap (fieldMap K t φ).toBoundedRingHom y) =
      BanachSpectrum.comap (transport K t φ).toBoundedRingHom
        ((boundedEquiv K B t).spectrumHomeomorph y) := by
  apply BanachSpectrum.ext
  intro a
  change y (toPresentation K B t
    (transport K t φ (fromPresentation K A t (toPresentation K A t a)))) =
      y (toPresentation K B t (transport K t φ a))
  rw [fromPresentation_toPresentation]

/-- The actual lifted domain locus in the coefficient-field presentation. -/
def fieldLocus (U : Domain K A) : Set (BanachSpectrum (presentation K A t)) :=
  (boundedEquiv K A t).spectrumHomeomorph ⁻¹' (liftedDomain K t U).locus

theorem range_fieldMap (U : Domain K A) :
    Set.range (BanachSpectrum.comap (fieldMap K t U.baseMap).toBoundedRingHom) =
      fieldLocus K t U := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    change (boundedEquiv K A t).spectrumHomeomorph
      (BanachSpectrum.comap (fieldMap K t U.baseMap).toBoundedRingHom y) ∈
        (liftedDomain K t U).locus
    rw [fieldMap_spectrum]
    exact (liftedDomain K t U).represents.hasImageIn _
  · intro x hx
    change (boundedEquiv K A t).spectrumHomeomorph x ∈ (liftedDomain K t U).locus at hx
    obtain ⟨y, hy⟩ := (liftedDomain K t U).represents.2.1.symm ▸ hx
    obtain ⟨z, hz⟩ := (boundedEquiv K U.algebra t).spectrumHomeomorph.surjective y
    refine ⟨z, (boundedEquiv K A t).spectrumHomeomorph.injective ?_⟩
    rw [fieldMap_spectrum, hz]
    exact hy

/-- The new coefficient-field presentation retains the full representation
property, including tests with arbitrary positive real radii. -/
theorem represents_fieldMap (U : Domain K A) :
    Represents (CompletedGaussLaurent K t) (fieldMap K t U.baseMap) (fieldLocus K t U) := by
  refine ⟨(liftedDomain K t U).represents.1.preimage
    (boundedEquiv K A t).spectrumHomeomorph.continuous, range_fieldMap K t U, ?_⟩
  intro R α hα
  let αold := α.comp (toPresentationOverExtension K A t)
  have hαold : ∀ x : BanachSpectrum R,
      BanachSpectrum.comap αold.toBoundedRingHom x ∈ (liftedDomain K t U).locus :=
    hα
  obtain ⟨β, hβ, huniq⟩ :=
    ScalarRestriction.existsUnique_factor_over_extension K (CompletedGaussLaurent K t)
      (LaurentAnnulus.presentation K t) (LaurentAnnulus.equivalence K t)
      (LaurentAnnulus.norm_equivalence K t) (algebra K A t) (algebra K U.algebra t)
      (transportOverExtension K t U.baseMap) (liftedDomain K t U).locus
      (represents_transport K t U) R αold hαold
  let βnew := β.comp (fromPresentationOverExtension K U.algebra t)
  have hβnew : βnew.comp (fieldMap K t U.baseMap) = α := by
    apply BoundedAlgHom.ext
    intro a
    change β (fromPresentation K U.algebra t
      (toPresentation K U.algebra t (transport K t U.baseMap
        (fromPresentation K A t a)))) = α a
    rw [fromPresentation_toPresentation]
    have h := congrArg (fun φ : BoundedAlgHom (CompletedGaussLaurent K t)
      (algebra K A t) R => φ (fromPresentation K A t a)) hβ
    exact h.trans (congrArg α (toPresentation_fromPresentation K A t a))
  refine ⟨βnew, hβnew, ?_⟩
  intro θ hθ
  let θold := θ.comp (toPresentationOverExtension K U.algebra t)
  have hθold : θold.comp (transportOverExtension K t U.baseMap) = αold := by
    apply BoundedAlgHom.ext
    intro a
    have h := congrArg (fun φ : BoundedAlgHom (CompletedGaussLaurent K t)
      (presentation K A t) R => φ (toPresentation K A t a)) hθ
    change θ (toPresentation K U.algebra t (transport K t U.baseMap
      (fromPresentation K A t (toPresentation K A t a)))) = _ at h
    rw [fromPresentation_toPresentation] at h
    exact h
  have h := huniq θold hθold
  apply BoundedAlgHom.ext
  intro b
  have hb := congrArg (fun φ : BoundedAlgHom (CompletedGaussLaurent K t)
    (algebra K U.algebra t) R => φ (fromPresentation K U.algebra t b)) h
  change θ (toPresentation K U.algebra t (fromPresentation K U.algebra t b)) =
    β (fromPresentation K U.algebra t b) at hb
  rwa [toPresentation_fromPresentation] at hb

/-- The actual full affinoid domain over the independent completed Laurent field. -/
def fieldDomain (U : Domain K A) :
    Domain (CompletedGaussLaurent K t) (presentation K A t) where
  algebra := presentation K U.algebra t
  baseMap := fieldMap K t U.baseMap
  locus := fieldLocus K t U
  represents := represents_fieldMap K t U

end RelativeLaurentAnnulus.ScalarExtension

end Langlands.Analytic
