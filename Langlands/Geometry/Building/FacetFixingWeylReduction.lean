import Langlands.Geometry.Building.PointParahoricNormalizer
import Mathlib.Algebra.Module.Submodule.Union

/-! # Chamber transport and affine Weyl images from facet fixing -/

noncomputable section

universe uH uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A locally finite reflection arrangement has a point on no root hyperplane,
including in rank zero. -/
theorem IsLocallyFiniteReflectionArrangement.exists_regularPoint
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) : ∃ x : A, IsRegular Ψ x := by
  classical
  let : Finite (derivativeRoots Ψ) := hΨ.finite_derivativeRoots.to_subtype
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun a : derivativeRoots Ψ => (a : Module.Dual ℝ V)) (by
      rintro ⟨a, ψ, hψ, rfl⟩
      by_contra h
      simp only [not_exists, not_not] at h
      exact hΨ.linear_ne_zero ψ hψ (LinearMap.ext h))
  obtain ⟨p⟩ : Nonempty A := inferInstance
  obtain ⟨ε, hε, hsign⟩ := exists_pos_of_eventually
    (eventually_sign_smul_vadd hΨ p u)
  refine ⟨ε • u +ᵥ p, fun ψ hψ => ?_⟩
  by_cases hp : ψ p = 0
  · rw [apply_smul_vadd, hp, zero_add]
    exact mul_ne_zero hε.ne' (hu ⟨ψ.linear, ψ, hψ, rfl⟩)
  · intro hz
    have hs := hsign ψ hψ hp
    rw [hz, sign_zero, eq_comm, sign_eq_zero_iff] at hs
    exact hp hs

/-- Choose a regular point of the given locally finite arrangement. -/
def regularPoint (hΨ : IsLocallyFiniteReflectionArrangement Ψ) : A :=
  Classical.choose hΨ.exists_regularPoint

theorem regularPoint_isRegular (hΨ : IsLocallyFiniteReflectionArrangement Ψ) :
    IsRegular Ψ (regularPoint hΨ) :=
  Classical.choose_spec hΨ.exists_regularPoint

/-- A chosen actual chamber, obtained without a positive-rank hypothesis. -/
def baseChamber (hΨ : IsLocallyFiniteReflectionArrangement Ψ) : Chambers Ψ :=
  ⟨facet Ψ (regularPoint hΨ), ⟨regularPoint hΨ, regularPoint_isRegular hΨ, rfl⟩⟩

/-- The unique affine Weyl element transporting a chosen chamber to its image
under a root-preserving affine automorphism. This is a map, not a homomorphism. -/
def chamberWeylTransport (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (C : Chambers Ψ) (e : rootStabilizer Ψ) : affineWeylGroup Ψ :=
  Classical.choose (Langlands.Geometry.Building.affineChamberSimpleTransitivity
    V A Ψ hΨ C.val ((e : A ≃ᵃ[ℝ] A) '' C.val) C.property
      (C.property.image e.property))

theorem chamberWeylTransport_image (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (C : Chambers Ψ) (e : rootStabilizer Ψ) :
    (chamberWeylTransport hΨ C e : A ≃ᵃ[ℝ] A) '' C.val =
      (e : A ≃ᵃ[ℝ] A) '' C.val :=
  (Classical.choose_spec (Langlands.Geometry.Building.affineChamberSimpleTransitivity
    V A Ψ hΨ C.val ((e : A ≃ᵃ[ℝ] A) '' C.val) C.property
      (C.property.image e.property))).1

theorem chamberWeylTransport_eq_iff (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (C : Chambers Ψ) (e : rootStabilizer Ψ) (w : affineWeylGroup Ψ) :
    w = chamberWeylTransport hΨ C e ↔
      (w : A ≃ᵃ[ℝ] A) '' C.val = (e : A ≃ᵃ[ℝ] A) '' C.val := by
  constructor
  · rintro rfl
    exact chamberWeylTransport_image hΨ C e
  · exact (Classical.choose_spec
      (Langlands.Geometry.Building.affineChamberSimpleTransitivity
        V A Ψ hΨ C.val ((e : A ≃ᵃ[ℝ] A) '' C.val) C.property
          (C.property.image e.property))).2 w

/-- If the action contains the affine Weyl group and preserves the roots,
pointwise fixing by the stabilizer of one chamber forces exact Weyl image. -/
theorem range_eq_affineWeylGroup_of_chamber_fixing
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {H : Type uH} [Group H] (f : H →* (A ≃ᵃ[ℝ] A))
    (hroot : f.range ≤ rootStabilizer Ψ)
    (hW : affineWeylGroup Ψ ≤ f.range)
    (C : Chambers Ψ)
    (hfix : ∀ n : H, f n '' C.val = C.val → ∀ x ∈ C.val, f n x = x) :
    f.range = affineWeylGroup Ψ := by
  apply le_antisymm ?_ hW
  rintro _ ⟨n, rfl⟩
  let e : rootStabilizer Ψ := ⟨f n, hroot ⟨n, rfl⟩⟩
  let w := chamberWeylTransport hΨ C e
  obtain ⟨m, hm⟩ := hW w.property
  have hw : (w : A ≃ᵃ[ℝ] A) '' C.val = f n '' C.val :=
    chamberWeylTransport_image hΨ C e
  have hcorr : f (m⁻¹ * n) '' C.val = C.val := by
    calc
      _ = (w : A ≃ᵃ[ℝ] A).symm '' (f n '' C.val) := by
        rw [map_mul, map_inv, hm, AffineEquiv.coe_mul, AffineEquiv.inv_def]
        exact (Set.image_image (w : A ≃ᵃ[ℝ] A).symm (f n) C.val).symm
      _ = (w : A ≃ᵃ[ℝ] A).symm '' ((w : A ≃ᵃ[ℝ] A) '' C.val) := by
        rw [hw]
      _ = C.val := by
        rw [Set.image_image]
        simp only [AffineEquiv.symm_apply_apply]
        exact Set.image_id _
  have hid : f (m⁻¹ * n) = 1 := by
    apply AffineEquiv.ext_on
      (C.property.affineSpan_eq_top hΨ.isLocallyFiniteReflectionArrangement)
    exact hfix (m⁻¹ * n) hcorr
  have heq : f n = (w : A ≃ᵃ[ℝ] A) := by
    rw [map_mul, map_inv, hm] at hid
    exact (inv_mul_eq_one.mp hid).symm
  rw [heq]
  exact w.property

/-- A root-preserving affine action containing the affine Weyl group has exactly
that image when every setwise facet stabilizer fixes its facet pointwise. -/
theorem range_eq_affineWeylGroup_of_facet_fixing
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {H : Type uH} [Group H] (f : H →* (A ≃ᵃ[ℝ] A))
    (hroot : f.range ≤ rootStabilizer Ψ)
    (hW : affineWeylGroup Ψ ≤ f.range)
    (hfix : ∀ C : Set A, IsFacet Ψ C →
      ∀ n : H, f n '' C = C → ∀ x ∈ C, f n x = x) :
    f.range = affineWeylGroup Ψ := by
  let C := baseChamber hΨ.isLocallyFiniteReflectionArrangement
  exact range_eq_affineWeylGroup_of_chamber_fixing hΨ f hroot hW C
    (hfix C.val C.property.isFacet)

end Langlands.Geometry.Building.AffineRootSystem
