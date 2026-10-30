import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Mathlib.CategoryTheory.Equivalence

/-! # Full represented domains under bounded equivalences of their bases -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem spectrum_precomp_symm (e : BoundedAlgEquiv K A B)
    (i : BoundedAlgHom K A C) (x : BanachSpectrum C) :
    e.spectrumHomeomorph
        (BanachSpectrum.comap (i.comp e.symm.toBoundedAlgHom).toBoundedRingHom x) =
      BanachSpectrum.comap i.toBoundedRingHom x := by
  apply BanachSpectrum.ext
  intro a
  change x (i (e.symm (e a))) = x (i a)
  rw [e.symm_apply_apply]

omit [CompleteSpace K] in
/-- Image containment in the transported locus is precisely image containment
for the map obtained by composing with the forward base equivalence. -/
theorem hasImageIn_precomp_equiv_iff (e : BoundedAlgEquiv K A B)
    (φ : BoundedAlgHom K B C) (U : Set (BanachSpectrum A)) :
    HasImageIn K φ (e.spectrumHomeomorph ⁻¹' U) ↔
      HasImageIn K (φ.comp e.toBoundedAlgHom) U := by
  have h (x : BanachSpectrum C) :
      e.spectrumHomeomorph (BanachSpectrum.comap φ.toBoundedRingHom x) =
        BanachSpectrum.comap (φ.comp e.toBoundedAlgHom).toBoundedRingHom x := by
    apply BanachSpectrum.ext
    intro a
    rfl
  constructor
  · intro hφ x
    have hx := hφ x
    change e.spectrumHomeomorph (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ U at hx
    rw [h x] at hx
    exact hx
  · intro hφ x
    change e.spectrumHomeomorph (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ U
    rw [h x]
    exact hφ x

/-- Changing the base by an actual bounded algebra equivalence preserves full
representation, with its exact transported spectrum locus. -/
theorem Represents.precomp_equiv {i : BoundedAlgHom K A C}
    {U : Set (BanachSpectrum A)} (hi : Represents K i U)
    (e : BoundedAlgEquiv K A B) :
    Represents K (i.comp e.symm.toBoundedAlgHom) (e.spectrumHomeomorph ⁻¹' U) := by
  refine ⟨hi.1.preimage e.spectrumHomeomorph.continuous, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change e.spectrumHomeomorph
        (BanachSpectrum.comap (i.comp e.symm.toBoundedAlgHom).toBoundedRingHom y) ∈ U
      rw [spectrum_precomp_symm]
      exact hi.hasImageIn y
    · intro hx
      obtain ⟨y, hy⟩ := hi.2.1.symm ▸ hx
      refine ⟨y, e.spectrumHomeomorph.injective ?_⟩
      rw [spectrum_precomp_symm]
      exact hy
  · intro R φ hφ
    have hφ' : HasImageIn K (φ.comp e.toBoundedAlgHom) U :=
      (hasImageIn_precomp_equiv_iff e φ U).1 hφ
    obtain ⟨ψ, hψ, huniq⟩ := hi.2.2 R (φ.comp e.toBoundedAlgHom) hφ'
    refine ⟨ψ, ?_, ?_⟩
    · apply BoundedAlgHom.ext
      intro b
      have h := congrArg (fun f : BoundedAlgHom K A R => f (e.symm b)) hψ
      simpa using h
    · intro χ hχ
      apply huniq
      apply BoundedAlgHom.ext
      intro a
      have h := congrArg (fun f : BoundedAlgHom K B R => f (e a)) hχ
      simpa using h

namespace Domain

/-- The quotient algebra is unchanged. The new structural map uses the inverse
bounded base map, and the new locus is the spectrum-homeomorphism preimage. -/
def transportBase (e : BoundedAlgEquiv K A B) (U : Domain K A) : Domain K B where
  algebra := U.algebra
  baseMap := U.baseMap.comp e.symm.toBoundedAlgHom
  locus := e.spectrumHomeomorph ⁻¹' U.locus
  represents := U.represents.precomp_equiv e

@[simp] theorem transportBase_algebra (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    (transportBase e U).algebra = U.algebra := rfl

@[simp] theorem transportBase_baseMap (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    (transportBase e U).baseMap = U.baseMap.comp e.symm.toBoundedAlgHom := rfl

@[simp] theorem transportBase_locus (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    (transportBase e U).locus = e.spectrumHomeomorph ⁻¹' U.locus := rfl

/-- Base transport keeps each actual bounded algebra restriction. -/
def transportBaseMap (e : BoundedAlgEquiv K A B) {U V : Domain K A} (f : U ⟶ V) :
    transportBase e U ⟶ transportBase e V where
  restriction := f.restriction
  comp_baseMap := by
    change f.restriction.comp (V.baseMap.comp e.symm.toBoundedAlgHom) =
      U.baseMap.comp e.symm.toBoundedAlgHom
    rw [← BoundedAlgHom.comp_assoc, f.comp_baseMap]

@[simp] theorem transportBaseMap_restriction (e : BoundedAlgEquiv K A B)
    {U V : Domain K A} (f : U ⟶ V) :
    (transportBaseMap e f).restriction = f.restriction := rfl

/-- The actual domain and restriction construction is functorial. -/
def transportBaseFunctor (e : BoundedAlgEquiv K A B) : Domain K A ⥤ Domain K B where
  obj := transportBase e
  map := transportBaseMap e
  map_id U := by apply Inclusion.ext; rfl
  map_comp f g := by apply Inclusion.ext; rfl

/-- The base spectrum triangle commutes for the unchanged quotient spectrum. -/
theorem transportBase_spectrumMap (e : BoundedAlgEquiv K A B) (U : Domain K A)
    (x : BanachSpectrum U.algebra) :
    e.spectrumHomeomorph ((transportBase e U).spectrumMap x) = U.spectrumMap x :=
  spectrum_precomp_symm e U.baseMap x

/-- The transported closed subspace is homeomorphic to the original locus. -/
def transportBaseLocusHomeomorph (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    (transportBase e U).locus ≃ₜ U.locus :=
  e.spectrumHomeomorph.sets rfl

/-- Compatibility with the actual maps from quotient spectra to their loci. -/
theorem transportBase_spectrumToLocus (e : BoundedAlgEquiv K A B) (U : Domain K A)
    (x : BanachSpectrum U.algebra) :
    transportBaseLocusHomeomorph e U ((transportBase e U).spectrumToLocus x) =
      U.spectrumToLocus x :=
  Subtype.ext (transportBase_spectrumMap e U x)

/-- The locus homeomorphisms commute with every actual domain restriction. -/
theorem transportBaseLocusHomeomorph_naturality (e : BoundedAlgEquiv K A B)
    {U V : Domain K A} (f : U ⟶ V) (x : (transportBase e U).locus) :
    transportBaseLocusHomeomorph e V ((transportBaseMap e f).locusMap x) =
      f.locusMap (transportBaseLocusHomeomorph e U x) := rfl

/-- Transport to the new base and back restores the structural algebra map. -/
theorem transportBase_symm_baseMap (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    (transportBase e.symm (transportBase e U)).baseMap = U.baseMap := by
  apply BoundedAlgHom.ext
  intro a
  change U.baseMap (e.symm (e a)) = U.baseMap a
  rw [e.symm_apply_apply]

/-- Round-trip transport restores the actual represented subset. -/
theorem transportBase_symm_locus (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    (transportBase e.symm (transportBase e U)).locus = U.locus := by
  ext x
  change e.spectrumHomeomorph (e.symm.spectrumHomeomorph x) ∈ U.locus ↔ x ∈ U.locus
  have h : e.spectrumHomeomorph (e.symm.spectrumHomeomorph x) = x := by
    apply BanachSpectrum.ext
    intro a
    change x (e.symm (e a)) = x a
    rw [e.symm_apply_apply]
  rw [h]

/-- The round-trip comparison is an actual domain isomorphism whose two
bounded restrictions are identities on the retained quotient algebra. -/
def transportBaseRoundTripIso (e : BoundedAlgEquiv K A B) (U : Domain K A) :
    transportBase e.symm (transportBase e U) ≅ U where
  hom := ⟨BoundedAlgHom.id K U.algebra, by
    change U.baseMap = (transportBase e.symm (transportBase e U)).baseMap
    exact (transportBase_symm_baseMap e U).symm⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, by
    change (transportBase e.symm (transportBase e U)).baseMap = U.baseMap
    exact transportBase_symm_baseMap e U⟩
  hom_inv_id := by apply Inclusion.ext; rfl
  inv_hom_id := by apply Inclusion.ext; rfl

/-- A bounded equivalence of actual bases constructs an equivalence between
categories of full domain representations. -/
def transportBaseEquivalence (e : BoundedAlgEquiv K A B) : Domain K A ≌ Domain K B where
  functor := transportBaseFunctor e
  inverse := transportBaseFunctor e.symm
  unitIso := NatIso.ofComponents (fun U => (transportBaseRoundTripIso e U).symm)
    (by intro U V f; apply Inclusion.ext; rfl)
  counitIso := NatIso.ofComponents (fun V => transportBaseRoundTripIso e.symm V)
    (by intro U V f; apply Inclusion.ext; rfl)
  functor_unitIso_comp U := by apply Inclusion.ext; rfl

/-- The algebra realization retains exactly the same quotient and restrictions. -/
theorem transportBaseFunctor_toAffinoidSpace (e : BoundedAlgEquiv K A B) :
    transportBaseFunctor e ⋙ toAffinoidSpace K B = toAffinoidSpace K A := rfl

/-- The actual quotient-spectrum realization is also unchanged. -/
theorem transportBaseFunctor_toTopologicalSpace (e : BoundedAlgEquiv K A B) :
    transportBaseFunctor e ⋙ toTopologicalSpace K B = toTopologicalSpace K A := rfl

end Domain
end Langlands.Analytic.PresentedAffinoidAlgebra
