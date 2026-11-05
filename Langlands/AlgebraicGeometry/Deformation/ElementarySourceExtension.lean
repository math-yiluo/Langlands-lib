import Langlands.AlgebraicGeometry.Deformation.ArtinianPolynomialPresentation
import Langlands.AlgebraicGeometry.Deformation.ArtinianElementaryKernel

/-! # The canonical elementary extension attached to an actual local presentation -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation.ElementarySourceExtension

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  (A : ArtinianTest k K) (π : R →ₐ[k] A.algebra)
  (hπ : A.augmentation.comp π = ε)

local notation "m" => IsLocalRing.maximalIdeal R

/-- The actual ideal of equations in the chosen local source. -/
abbrev equations : Ideal R := RingHom.ker π.toRingHom

/-- The ideal defining the canonical elementary source extension. -/
def sourceIdeal : Ideal R := m * equations A π

lemma sourceIdeal_le_equations : sourceIdeal A π ≤ equations A π :=
  Ideal.mul_le_right

include hπ in
omit [IsLocalRing R] in
lemma equations_le_augmentation : equations A π ≤ RingHom.ker ε.toRingHom := by
  intro r hr
  change ε r = 0
  rw [← hπ]
  change A.augmentation (π r) = 0
  have hr' : π r = 0 := RingHom.mem_ker.mp hr
  rw [hr', map_zero]

include hπ in
lemma sourceIdeal_le_augmentation : sourceIdeal A π ≤ RingHom.ker ε.toRingHom :=
  (sourceIdeal_le_equations A π).trans (equations_le_augmentation ε A π hπ)

/-- The original augmentation on the canonical quotient. -/
def augmentation : R ⧸ sourceIdeal A π →ₐ[k] K :=
  Ideal.Quotient.liftₐ _ ε
    (fun _ hx ↦ RingHom.mem_ker.mp (sourceIdeal_le_augmentation ε A π hπ hx))

include hε in
lemma augmentation_surjective : Function.Surjective (augmentation ε A π hπ) := by
  intro a
  obtain ⟨r, hr⟩ := hε a
  exact ⟨Ideal.Quotient.mk _ r, hr⟩

include hε hπ in
/-- The defining ideal still contains a positive maximal-ideal power. -/
lemma exists_power_le_sourceIdeal :
    ∃ n : ℕ, m ^ (n + 1) ≤ sourceIdeal A π := by
  obtain ⟨n, hn⟩ := LocalAdicArtinianTests.exists_bound ε hε π hπ
  refine ⟨n + 1, ?_⟩
  rw [pow_succ']
  exact mul_le_mul' le_rfl hn

variable {B : ArtinianTest k K} (q : B ⟶ A) (β : R →ₐ[k] B.algebra)

include hπ in
omit [IsLocalRing R] in
/-- Any actual algebra lift over `A` automatically retains the original residue
augmentation. -/
lemma lift_augmentation
    (hβ : (ArtinianTest.toAlgHom q).comp β = π) :
    B.augmentation.comp β = ε := by
  rw [← ArtinianTest.augmentation_comp q, AlgHom.comp_assoc, hβ, hπ]

include hε hπ in
/-- Every lift of the local presentation through an elementary arrow kills the
canonical source ideal. No surjectivity of the lift is assumed. -/
lemma sourceIdeal_le_ker_lift (hq : ArtinianTest.IsElementarySurjection q)
    (hβ : (ArtinianTest.toAlgHom q).comp β = π) :
    sourceIdeal A π ≤ RingHom.ker β.toRingHom := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [sourceIdeal, Ideal.map_mul]
  have hm : (m).map β.toRingHom ≤ IsLocalRing.maximalIdeal B.algebra := by
    rw [← ArtinianTest.ker_augmentation B, Ideal.map_le_iff_le_comap]
    intro r hr
    change B.augmentation (β r) = 0
    have hr' : ε r = 0 := RingHom.mem_ker.mp
      ((IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε).symm ▸ hr)
    exact (DFunLike.congr_fun (lift_augmentation ε A π hπ q β hβ) r).trans hr'
  have hJ : (equations A π).map β.toRingHom ≤
      RingHom.ker (ArtinianTest.toAlgHom q).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change ArtinianTest.toAlgHom q (β r) = 0
    exact (DFunLike.congr_fun hβ r).trans (RingHom.mem_ker.mp hr)
  exact (mul_le_mul' hm hJ).trans_eq hq.2

variable [IsNoetherianRing R]

include hε hπ in
/-- The canonical source quotient is Artinian, using actual nilpotence in the
given target test and Noetherianity of the local source. -/
lemma quotient_artinian : IsArtinianRing (R ⧸ sourceIdeal A π) := by
  have : Nontrivial (R ⧸ sourceIdeal A π) :=
    (augmentation ε A π hπ).toRingHom.domain_nontrivial
  have : IsLocalRing (R ⧸ sourceIdeal A π) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (R ⧸ sourceIdeal A π) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := exists_power_le_sourceIdeal ε hε A π hπ
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
  refine ⟨n + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (sourceIdeal A π)) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le hn

/-- The actual augmented Artinian source test `R/(m ker π)`. -/
def test : ArtinianTest k K := by
  have : Nontrivial (R ⧸ sourceIdeal A π) :=
    (augmentation ε A π hπ).toRingHom.domain_nontrivial
  have : IsLocalRing (R ⧸ sourceIdeal A π) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have := quotient_artinian ε hε A π hπ
  exact ArtinianTest.mk (R ⧸ sourceIdeal A π) (augmentation ε A π hπ)
    (augmentation_surjective ε hε A π hπ)

/-- The actual quotient map from the original local source. -/
def projection : R →ₐ[k] (test ε hε A π hπ).algebra :=
  Ideal.Quotient.mkₐ k (sourceIdeal A π)

lemma projection_surjective : Function.Surjective (projection ε hε A π hπ) :=
  Ideal.Quotient.mkₐ_surjective k _

lemma augmentation_projection :
    (test ε hε A π hπ).augmentation.comp (projection ε hε A π hπ) = ε :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The canonical actual test arrow to the original Artinian test. -/
def reduction : test ε hε A π hπ ⟶ A :=
  ArtinianTest.homMk
    (Ideal.Quotient.liftₐ _ π
      (fun _ hx ↦ RingHom.mem_ker.mp (sourceIdeal_le_equations A π hx))) (by
        apply Ideal.Quotient.algHom_ext
        exact hπ)

lemma reduction_projection :
    (ArtinianTest.toAlgHom (reduction ε hε A π hπ)).comp
      (projection ε hε A π hπ) = π :=
  Ideal.Quotient.liftₐ_comp _ _ _

lemma reduction_surjective (h : Function.Surjective π) :
    Function.Surjective (ArtinianTest.toAlgHom (reduction ε hε A π hπ)) := by
  intro a
  obtain ⟨r, hr⟩ := h a
  exact ⟨Ideal.Quotient.mk _ r, hr⟩

/-- The actual kernel is the image of the actual equation ideal, namely
`ker π/(m ker π)` as a subgroup of the quotient source. -/
lemma ker_reduction :
    RingHom.ker (ArtinianTest.toAlgHom (reduction ε hε A π hπ)).toRingHom =
      (equations A π).map (Ideal.Quotient.mk (sourceIdeal A π)) := by
  change RingHom.ker (Ideal.Quotient.lift _ π.toRingHom _) = _
  exact Ideal.ker_quotient_lift _ _

/-- A surjective presentation produces an elementary surjection of actual
augmented Artinian tests. -/
lemma reduction_elementary (h : Function.Surjective π) :
    ArtinianTest.IsElementarySurjection (reduction ε hε A π hπ) := by
  refine ⟨reduction_surjective ε hε A π hπ h, ?_⟩
  rw [ker_reduction]
  have : IsLocalRing (R ⧸ sourceIdeal A π) :=
    inferInstanceAs (IsLocalRing (test ε hε A π hπ).algebra)
  change IsLocalRing.maximalIdeal (R ⧸ sourceIdeal A π) *
    (equations A π).map (Ideal.Quotient.mk (sourceIdeal A π)) = ⊥
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (sourceIdeal A π)) Ideal.Quotient.mk_surjective,
    ← Ideal.map_mul]
  exact Ideal.map_mk_eq_bot_of_le (le_refl (sourceIdeal A π))

/-- The actual kernel of the canonical extension has its canonical finite
residue-field module structure. -/
lemma kernel_finiteDimensional (h : Function.Surjective π) :
    letI := ArtinianTest.ElementaryKernel.residueModule
      (reduction ε hε A π hπ) (reduction_elementary ε hε A π hπ h)
    FiniteDimensional K
      (ArtinianTest.ElementaryKernel.Kernel (reduction ε hε A π hπ)) :=
  ArtinianTest.ElementaryKernel.finiteDimensional _ _

/-- The unique actual augmented factor of an algebra lift through the canonical
elementary source test. -/
def factor (hq : ArtinianTest.IsElementarySurjection q)
    (hβ : (ArtinianTest.toAlgHom q).comp β = π) :
    test ε hε A π hπ ⟶ B :=
  ArtinianTest.homMk
    (Ideal.Quotient.liftₐ _ β (fun _ hx ↦
      RingHom.mem_ker.mp (sourceIdeal_le_ker_lift ε hε A π hπ q β hq hβ hx))) (by
        apply Ideal.Quotient.algHom_ext
        exact lift_augmentation ε A π hπ q β hβ)

lemma factor_projection (hq : ArtinianTest.IsElementarySurjection q)
    (hβ : (ArtinianTest.toAlgHom q).comp β = π) :
    (ArtinianTest.toAlgHom (factor ε hε A π hπ q β hq hβ)).comp
      (projection ε hε A π hπ) = β :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The factor still lies over the original test `A`. -/
lemma factor_reduction (hq : ArtinianTest.IsElementarySurjection q)
    (hβ : (ArtinianTest.toAlgHom q).comp β = π) :
    factor ε hε A π hπ q β hq hβ ≫ q = reduction ε hε A π hπ := by
  apply ArtinianTest.hom_ext
  apply Ideal.Quotient.algHom_ext
  exact hβ

/-- Its original local-source composite determines the factor uniquely. -/
lemma factor_unique (hq : ArtinianTest.IsElementarySurjection q)
    (hβ : (ArtinianTest.toAlgHom q).comp β = π)
    (γ : test ε hε A π hπ ⟶ B)
    (hγ : (ArtinianTest.toAlgHom γ).comp (projection ε hε A π hπ) = β) :
    γ = factor ε hε A π hπ q β hq hβ := by
  apply ArtinianTest.hom_ext
  apply Ideal.Quotient.algHom_ext
  exact hγ

/-- Every local-source lift along an elementary arrow factors uniquely as an
actual test arrow over `A`. -/
lemma existsUnique_factor (hq : ArtinianTest.IsElementarySurjection q)
    (hβ : (ArtinianTest.toAlgHom q).comp β = π) :
    ∃! γ : test ε hε A π hπ ⟶ B,
      (ArtinianTest.toAlgHom γ).comp (projection ε hε A π hπ) = β ∧
        γ ≫ q = reduction ε hε A π hπ :=
  ⟨factor ε hε A π hπ q β hq hβ,
    ⟨factor_projection ε hε A π hπ q β hq hβ,
      factor_reduction ε hε A π hπ q β hq hβ⟩,
    fun γ hγ ↦ factor_unique ε hε A π hπ q β hq hβ γ hγ.1⟩

section Polynomial

variable [IsNoetherianRing k] [Module.Finite k K]

/-- The canonical elementary source test of the actual surjective completed
polynomial presentation of the whole test `A`. -/
abbrev polynomialTest : ArtinianTest k K :=
  test (ArtinianPolynomialPresentation.augmentation A)
    (ArtinianPolynomialPresentation.augmentation_surjective A) A
    (ArtinianPolynomialPresentation.cover A)
    (ArtinianPolynomialPresentation.augmentation_cover A)

/-- The genuine quotient from the completed polynomial source onto its
canonical elementary source test. -/
abbrev polynomialProjection :
    ArtinianPolynomialPresentation.ring A →ₐ[k] (polynomialTest A).algebra :=
  projection (ArtinianPolynomialPresentation.augmentation A)
    (ArtinianPolynomialPresentation.augmentation_surjective A) A
    (ArtinianPolynomialPresentation.cover A)
    (ArtinianPolynomialPresentation.augmentation_cover A)

/-- The actual augmentation-preserving elementary arrow to the unchanged test. -/
abbrev polynomialReduction : polynomialTest A ⟶ A :=
  reduction (ArtinianPolynomialPresentation.augmentation A)
    (ArtinianPolynomialPresentation.augmentation_surjective A) A
    (ArtinianPolynomialPresentation.cover A)
    (ArtinianPolynomialPresentation.augmentation_cover A)

lemma polynomialReduction_elementary :
    ArtinianTest.IsElementarySurjection (polynomialReduction A) :=
  reduction_elementary _ _ _ _ _ (ArtinianPolynomialPresentation.cover_surjective A)

lemma polynomialReduction_projection :
    (ArtinianTest.toAlgHom (polynomialReduction A)).comp (polynomialProjection A) =
      ArtinianPolynomialPresentation.cover A :=
  reduction_projection _ _ _ _ _

end Polynomial

end Langlands.AlgebraicGeometry.Deformation.ElementarySourceExtension
