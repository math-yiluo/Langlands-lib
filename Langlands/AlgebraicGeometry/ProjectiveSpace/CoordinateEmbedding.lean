import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Coordinate embeddings of projective spaces

A graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` that is surjective in every degree induces a
closed immersion `Proj ℬ ⟶ Proj 𝒜`. For an injective map of coordinate indices
`e : Fin (a + 1) → Fin (N + 1)`, the substitution `X k ↦ X j` for `k = e j`, and `X k ↦ 0`
for `k` outside the range of `e`, is such a homomorphism. It gives a closed immersion
`ProjectiveSpace R a ⟶ ProjectiveSpace R N` over `Spec R`, onto the linear subspace where all
coordinates outside the range of `e` vanish.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

section Generic

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hsurj : ∀ (i : ℕ) (y : B), y ∈ ℬ i → ∃ x ∈ 𝒜 i, f x = y)

include hsurj in
/-- A graded homomorphism that is surjective in every degree satisfies the irrelevant-ideal
condition of `Proj.map`. -/
theorem irrelevant_le_map_of_surjective :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi y hy
  obtain ⟨x, hx, rfl⟩ := hsurj i y hy
  have hx' := HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi hx
  have h := Ideal.mem_map_of_mem f.toRingHom hx'
  change f x ∈ Ideal.map f.toRingHom (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  simpa only [GradedRingHom.coe_toRingHom] using h

include hsurj in
/-- A graded homomorphism that is surjective in every degree is surjective on the degree-zero
localizations away from a homogeneous element. -/
theorem away_map_surjective {i : ℕ} (s : A) (hs : s ∈ 𝒜 i) :
    Function.Surjective (Away.map f s) := by
  intro y
  obtain ⟨n, y, hy, rfl⟩ := y.mk_surjective _ (f.2 hs)
  obtain ⟨x, hx, rfl⟩ := hsurj _ y hy
  exact ⟨Away.mk 𝒜 hs n x hx, Away.map_mk _ _ _ _ _ _⟩

variable {f} in
/-- Over the chart `Spec A[s⁻¹]₀ ⟶ Proj 𝒜`, the morphism `Proj.map f` is the spectrum of the
localized map `A[s⁻¹]₀ ⟶ B[f(s)⁻¹]₀`. -/
theorem isPullback_awayι_map
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    IsPullback (Proj.awayι ℬ (f s) (f.2 hs) hi) (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Proj.map f hf) (Proj.awayι 𝒜 s hs hi) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map f hf hi s hs) ?_).flip
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  exact Proj.map_preimage_basicOpen f hf s

/-- A graded homomorphism that is surjective in every degree induces a closed immersion of
`Proj`s. -/
theorem isClosedImmersion_map_of_surjective :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hsurj)) := by
  refine IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover fun s => ?_
  have hpb := isPullback_awayι_map (irrelevant_le_map_of_surjective f hsurj) s.1.2 s.2 s.2.2
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s.2))) :=
    IsClosedImmersion.spec_of_surjective _ (away_map_surjective f hsurj s.2 s.2.2)
  have h2 : IsClosedImmersion
      (hpb.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Away.map f s.2))) := inferInstance
  rw [hpb.isoPullback_inv_snd] at h2
  exact h2

end Generic

variable (R : Type u) [CommRing R] {a N : ℕ} (e : Fin (a + 1) → Fin (N + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate images of the restriction: `X k ↦ X j` when `k = e j`, and `X k ↦ 0` when
`k` is not in the range of `e`. -/
def coordinateImage : Fin (N + 1) → ProjectiveCoordinateRing R a :=
  Function.extend e MvPolynomial.X 0

/-- The substitution `X k ↦ coordinateImage R e k` of homogeneous coordinates. -/
def coordinateRestriction :
    ProjectiveCoordinateRing R N →ₐ[R] ProjectiveCoordinateRing R a :=
  MvPolynomial.aeval (coordinateImage R e)

lemma isHomogeneous_coordinateImage (k : Fin (N + 1)) :
    (coordinateImage R e k).IsHomogeneous 1 := by
  rw [coordinateImage, Function.extend_def]
  split_ifs
  · exact MvPolynomial.isHomogeneous_X R _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/-- The coordinate restriction as a graded ring homomorphism. -/
def gradedCoordinateRestriction :
    projectiveSpaceGrading R N →+*ᵍ projectiveSpaceGrading R a where
  toRingHom := (coordinateRestriction R e).toRingHom
  map_mem {i} {x} hx := by
    have hhom := (MvPolynomial.mem_homogeneousSubmodule i x).mp hx
    have h := hhom.aeval (coordinateImage R e) (isHomogeneous_coordinateImage R e)
    exact (MvPolynomial.mem_homogeneousSubmodule i _).mpr (by
      simpa [coordinateRestriction] using h)

lemma gradedCoordinateRestriction_apply (x : ProjectiveCoordinateRing R N) :
    gradedCoordinateRestriction R e x = coordinateRestriction R e x := rfl

lemma coordinateRestriction_X (k : Fin (N + 1)) :
    coordinateRestriction R e (MvPolynomial.X k) = coordinateImage R e k :=
  MvPolynomial.aeval_X _ _

lemma coordinateRestriction_C (r : R) :
    coordinateRestriction R e (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [coordinateRestriction]

variable {e}

lemma coordinateImage_apply (he : Function.Injective e) (j : Fin (a + 1)) :
    coordinateImage R e (e j) = MvPolynomial.X j :=
  he.extend_apply _ _ j

lemma coordinateImage_of_not_mem (k : Fin (N + 1)) (hk : ∀ j, e j ≠ k) :
    coordinateImage R e k = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hk j hj

/-- Renaming the variables along `e` is a section of the coordinate restriction. -/
lemma coordinateRestriction_rename (he : Function.Injective e)
    (x : ProjectiveCoordinateRing R a) :
    coordinateRestriction R e (MvPolynomial.rename e x) = x := by
  rw [coordinateRestriction, MvPolynomial.aeval_rename]
  have : coordinateImage R e ∘ e = MvPolynomial.X :=
    funext fun j => coordinateImage_apply R he j
  rw [this, MvPolynomial.aeval_X_left_apply]

lemma exists_preimage (he : Function.Injective e) (i : ℕ) (y : ProjectiveCoordinateRing R a)
    (hy : y ∈ projectiveSpaceGrading R a i) :
    ∃ x ∈ projectiveSpaceGrading R N i, gradedCoordinateRestriction R e x = y :=
  ⟨MvPolynomial.rename e y, (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    ((MvPolynomial.mem_homogeneousSubmodule i y).mp hy).rename_isHomogeneous,
    coordinateRestriction_rename R he y⟩

/-- The coordinate embedding `ProjectiveSpace R a ⟶ ProjectiveSpace R N` given by an injective
map of coordinate indices `e`. -/
def coordinateEmbedding (he : Function.Injective e) :
    ProjectiveSpace R a ⟶ ProjectiveSpace R N :=
  Proj.map (gradedCoordinateRestriction R e)
    (irrelevant_le_map_of_surjective _ (exists_preimage R he))

instance isClosedImmersion_coordinateEmbedding (he : Function.Injective e) :
    IsClosedImmersion (coordinateEmbedding R he) :=
  isClosedImmersion_map_of_surjective _ (exists_preimage R he)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinate embedding is a morphism over `Spec R`. -/
theorem coordinateEmbedding_toSpec (he : Function.Injective e) :
    coordinateEmbedding R he ≫ projectiveSpaceToSpec R N = projectiveSpaceToSpec R a := by
  refine (Proj.mapAffineOpenCover (gradedCoordinateRestriction R e)
    (irrelevant_le_map_of_surjective _ (exists_preimage R he))).openCover.hom_ext _ _
    fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    coordinateEmbedding, projectiveSpaceToSpec,
    Proj.awayι_comp_map_assoc (gradedCoordinateRestriction R e) _ s.1.2 _ s.2.2,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext r
  simp [Away.map, HomogeneousLocalization.map_mk, fromZeroRingHom,
    gradedCoordinateRestriction_apply, projectiveSpaceConstants]

theorem coordinateEmbedding_preimage (he : Function.Injective e) (k : Fin (N + 1)) :
    coordinateEmbedding R he ⁻¹ᵁ projectiveSpaceCoordinateOpen R N k =
      Proj.basicOpen (projectiveSpaceGrading R a) (coordinateImage R e k) := by
  rw [← coordinateRestriction_X, ← gradedCoordinateRestriction_apply]
  rfl

/-- The coordinate embedding pulls the coordinate open `D₊(X (e j))` back to `D₊(X j)`. -/
theorem coordinateEmbedding_preimage_apply (he : Function.Injective e) (j : Fin (a + 1)) :
    coordinateEmbedding R he ⁻¹ᵁ projectiveSpaceCoordinateOpen R N (e j) =
      projectiveSpaceCoordinateOpen R a j := by
  rw [coordinateEmbedding_preimage, coordinateImage_apply R he]
  rfl

/-- The coordinate embedding misses the coordinate opens of indices outside the range of
`e`. -/
theorem coordinateEmbedding_preimage_eq_bot (he : Function.Injective e) (k : Fin (N + 1))
    (hk : ∀ j, e j ≠ k) :
    coordinateEmbedding R he ⁻¹ᵁ projectiveSpaceCoordinateOpen R N k = ⊥ := by
  rw [coordinateEmbedding_preimage, coordinateImage_of_not_mem R k hk, Proj.basicOpen_zero]
  rfl

end Langlands.AlgebraicGeometry.ProjectiveSpace
