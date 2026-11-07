import Langlands.Algebra.IntegralAlgebraPrimeAvoidance
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.Spectrum.Prime.Topology

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry

/-- The image of the spectrum of an integral field algebra in an affine
scheme has a principal neighborhood inside every open neighborhood. -/
theorem exists_basicOpen_of_integral_field_algebra
    {k R A : Type*} [Field k] [CommRing R] [CommRing A]
    [Algebra k A] [Algebra.IsIntegral k A] (φ : R →+* A)
    (W : Opens (PrimeSpectrum R)) (hW : ∀ p, PrimeSpectrum.comap φ p ∈ W) :
    ∃ r : R, (∀ p, PrimeSpectrum.comap φ p ∈ PrimeSpectrum.basicOpen r) ∧
      PrimeSpectrum.basicOpen r ≤ W := by
  let I : Ideal R := PrimeSpectrum.vanishingIdeal (W : Set (PrimeSpectrum R))ᶜ
  have hI : I.map φ = ⊤ := by
    apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp' : PrimeSpectrum.comap φ p ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
      intro r hr
      exact hp (Ideal.mem_map_of_mem φ hr)
    have heq : PrimeSpectrum.zeroLocus (I : Set R) = (W : Set (PrimeSpectrum R))ᶜ := by
      exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
        W.isOpen.isClosed_compl.closure_eq
    rw [heq] at hp'
    exact hp' (hW p)
  obtain ⟨r, hr, hu⟩ :=
    Langlands.Algebra.exists_isUnit_of_map_eq_top_of_integral_field (k := k) φ I hI
  refine ⟨r, ?_, ?_⟩
  · intro p
    change φ r ∉ p.asIdeal
    intro hp
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hp hu)
  · intro p hp
    by_contra hpW
    exact hp ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hr p hpW)

/-- The scheme version of integral-field prime avoidance on an affine target. -/
theorem exists_basicOpen_of_integral_field_scheme
    {k : Type u} [Field k] {T X : Scheme.{u}} [IsAffine T] [IsAffine X]
    [Algebra k Γ(T, ⊤)] [Algebra.IsIntegral k Γ(T, ⊤)]
    (f : T ⟶ X) (W : X.Opens) (hW : ∀ t, f t ∈ W) :
    ∃ s : Γ(X, ⊤), (∀ t, f t ∈ X.basicOpen s) ∧ X.basicOpen s ≤ W := by
  let W' : (Spec Γ(X, ⊤)).Opens := X.isoSpec.inv ⁻¹ᵁ W
  have hW' (p : PrimeSpectrum Γ(T, ⊤)) :
      PrimeSpectrum.comap f.appTop.hom p ∈ W' := by
    have h := congrArg (fun g : Spec Γ(T, ⊤) ⟶ X => g p)
      (Scheme.isoSpec_inv_naturality f)
    change X.isoSpec.inv (PrimeSpectrum.comap f.appTop.hom p) ∈ W
    rw [show X.isoSpec.inv (PrimeSpectrum.comap f.appTop.hom p) =
      f (T.isoSpec.inv p) from h]
    exact hW _
  obtain ⟨s, hs, hsW⟩ :=
    exists_basicOpen_of_integral_field_algebra (k := k) f.appTop.hom W' hW'
  refine ⟨s, ?_, ?_⟩
  · intro t
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    have h := congrArg (fun g : T ⟶ Spec Γ(X, ⊤) => g t)
      (Scheme.toSpecΓ_naturality f)
    change X.toSpecΓ (f t) ∈ PrimeSpectrum.basicOpen s
    rw [show X.toSpecΓ (f t) =
      PrimeSpectrum.comap f.appTop.hom (T.toSpecΓ t) from h]
    exact hs _
  · intro x hx
    rw [← Scheme.toSpecΓ_preimage_basicOpen] at hx
    have h := hsW hx
    change X.isoSpec.inv (X.toSpecΓ x) ∈ W at h
    have heq : X.isoSpec.inv (X.toSpecΓ x) = x :=
      congrArg (fun g : X ⟶ X => g x) X.toSpecΓ_isoSpec_inv
    rwa [heq] at h

/-- An integral morphism to the spectrum of a field supplies the integral
global-section algebra needed for principal neighborhoods of its image. -/
theorem exists_basicOpen_of_integral_field_morphism
    {k : Type u} [Field k] {T X : Scheme.{u}} [IsAffine X]
    (p : T ⟶ Spec (CommRingCat.of k)) [IsIntegralHom p]
    (f : T ⟶ X) (W : X.Opens) (hW : ∀ t, f t ∈ W) :
    ∃ s : Γ(X, ⊤), (∀ t, f t ∈ X.basicOpen s) ∧ X.basicOpen s ≤ W := by
  let : IsAffine T := isAffine_of_isAffineHom p
  let φ := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop
  have hφ : φ.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact p.isIntegral_app ⊤ (isAffineOpen_top _)
  let := φ.hom.toAlgebra
  let : Algebra.IsIntegral k Γ(T, ⊤) := ⟨hφ⟩
  exact exists_basicOpen_of_integral_field_scheme (k := k) f W hW

/-- Inside an affine open containing an integral fibre, any open containing
that fibre contains a principal neighborhood of the whole fibre. -/
theorem exists_basicOpen_of_integral_fibre_in_affineOpen
    {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsIntegralHom j] (y : Y)
    (U : Z.Opens) (hU : IsAffineOpen U)
    (hFU : ∀ z : Z, j z = y → z ∈ U)
    (W : Z.Opens) (hFW : ∀ z : Z, j z = y → z ∈ W) :
    ∃ s : Γ(Z, U), (∀ z : Z, j z = y → z ∈ Z.basicOpen s) ∧
      Z.basicOpen s ≤ W := by
  let : IsAffine U.toScheme := hU
  have hF (t : j.fiber y) : j (j.fiberι y t) = y := by
    have ht : j.fiberι y t ∈ Set.range (j.fiberι y) := ⟨t, rfl⟩
    rwa [j.range_fiberι] at ht
  have hFU' : Set.range (j.fiberι y) ⊆ Set.range U.ι := by
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨_, hFU _ (hF t)⟩, rfl⟩
  let f : j.fiber y ⟶ U.toScheme := IsOpenImmersion.lift U.ι (j.fiberι y) hFU'
  have hf (t : j.fiber y) : U.ι (f t) = j.fiberι y t :=
    congrArg (fun g : j.fiber y ⟶ Z => g t) (IsOpenImmersion.lift_fac _ _ hFU')
  have : IsIntegralHom (j.fiberToSpecResidueField y) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  obtain ⟨s, hsF, hsW⟩ := exists_basicOpen_of_integral_field_morphism
    (k := Y.residueField y) (T := j.fiber y) (X := U.toScheme)
    (j.fiberToSpecResidueField y) f (U.ι ⁻¹ᵁ W) (fun t => by
      change U.ι (f t) ∈ W
      rw [hf]
      exact hFW _ (hF t))
  have himage : U.ι ''ᵁ U.toScheme.basicOpen s = Z.basicOpen (U.topIso.hom s) := by
    have hc : U.topIso.inv (U.topIso.hom s) = s := by
      change (U.topIso.hom ≫ U.topIso.inv) s = s
      rw [U.topIso.hom_inv_id]
      rfl
    have h := U.ι_image_basicOpen_topIso_inv (U.topIso.hom s)
    rwa [hc] at h
  refine ⟨U.topIso.hom s, ?_, ?_⟩
  · intro z hz
    let t := (j.fiberHomeo y).symm ⟨z, hz⟩
    rw [← himage]
    refine ⟨f t, hsF t, ?_⟩
    change U.ι (f t) = z
    rw [hf, Scheme.Hom.fiberι_fiberHomeo_symm]
  · rw [← himage]
    rintro _ ⟨x, hx, rfl⟩
    exact hsW hx

/-- A chosen section cutting out a principal neighborhood of an integral fibre. -/
noncomputable def integralFibrePrincipalNeighborhood
    {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsIntegralHom j] (y : Y)
    (U : Z.Opens) (hU : IsAffineOpen U)
    (hFU : ∀ z : Z, j z = y → z ∈ U)
    (W : Z.Opens) (hFW : ∀ z : Z, j z = y → z ∈ W) :
    {s : Γ(Z, U) // (∀ z : Z, j z = y → z ∈ Z.basicOpen s) ∧
      Z.basicOpen s ≤ W} :=
  ⟨Classical.choose (exists_basicOpen_of_integral_fibre_in_affineOpen j y U hU hFU W hFW),
    Classical.choose_spec (exists_basicOpen_of_integral_fibre_in_affineOpen j y U hU hFU W hFW)⟩

end Langlands.AlgebraicGeometry
