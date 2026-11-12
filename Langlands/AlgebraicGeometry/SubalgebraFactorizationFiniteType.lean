import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Langlands.AlgebraicGeometry.Picard.AffineIsomColimit
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Adjoin.FG

/-! # Local finite type from factorizations through finitely generated subalgebras -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `B₁` be a finitely generated `R`-subalgebra of an `R`-algebra `B`, and let `U` be an open
subset of `Spec B₁` containing the image of `Spec B`. Then some finitely generated subalgebra
`B₂ ⊇ B₁` of `B` already has its image in `U`. -/
theorem exists_subalgebra_comap_mem_of_isOpen {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (B₁ : Subalgebra R B) (hB₁ : B₁.FG) (U : Set (PrimeSpectrum B₁))
    (hU : IsOpen U) (h : ∀ p : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap B₁ B) p ∈ U) :
    ∃ (B₂ : Subalgebra R B) (_ : B₂.FG) (hle : B₁ ≤ B₂),
      ∀ p : PrimeSpectrum B₂,
        PrimeSpectrum.comap (Subalgebra.inclusion hle).toRingHom p ∈ U := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).mp hU.isClosed_compl
  have htop : I.map (algebraMap B₁ B) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hp := h ⟨m, hm.isPrime⟩
    have hc : PrimeSpectrum.comap (algebraMap B₁ B) ⟨m, hm.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus]
      intro x hx
      exact hle (Ideal.mem_map_of_mem _ hx)
    exact hc hp
  have h1 : (1 : B) ∈ Submodule.span B ((algebraMap B₁ B) '' (I : Set B₁)) := by
    change (1 : B) ∈ I.map (algebraMap B₁ B)
    rw [htop]
    trivial
  obtain ⟨T, hTsub, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hT
  -- preimages of the elements of `T` in `I`
  have hpre : ∀ t ∈ T, ∃ x : B₁, x ∈ I ∧ algebraMap B₁ B x = t := fun t ht ↦ hTsub ht
  choose x hxI hxt using hpre
  let B₂ : Subalgebra R B := B₁ ⊔ Algebra.adjoin R ((T.image c : Finset B) : Set B)
  have hB₂ : B₂.FG := hB₁.sup (Subalgebra.fg_adjoin_finset _)
  have hle : B₁ ≤ B₂ := le_sup_left
  refine ⟨B₂, hB₂, hle, fun p ↦ ?_⟩
  by_contra hp
  have hp' : PrimeSpectrum.comap (Subalgebra.inclusion hle).toRingHom p ∈ Uᶜ := hp
  rw [hI, PrimeSpectrum.mem_zeroLocus] at hp'
  have hcmem : ∀ t ∈ T, c t ∈ B₂ := fun t ht ↦
    (le_sup_right : Algebra.adjoin R _ ≤ B₂)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem c ht)))
  -- the element `∑ c t * x t` of `B₂` lies in `p` and equals `1`
  let s : B₂ := ∑ t ∈ T.attach,
    (⟨c t, hcmem t t.2⟩ : B₂) * Subalgebra.inclusion hle (x t t.2)
  have hs : s ∈ p.asIdeal := by
    refine Ideal.sum_mem _ fun t _ ↦ Ideal.mul_mem_left _ _ ?_
    exact hp' (hxI t t.2)
  have hs1 : s = 1 := by
    apply Subtype.val_injective
    simp only [s, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      Subalgebra.coe_inclusion, OneMemClass.coe_one]
    rw [← hc, ← Finset.sum_attach T (fun a ↦ c a • a)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    exact congrArg (c ↑t * ·) (hxt t t.2)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hs1 ▸ hs))

open Langlands.AlgebraicGeometry.Picard

/-- Scheme form of `exists_subalgebra_comap_mem_of_isOpen`: if an open subset of the affine
stage `Spec B₁` contains the image of `Spec B`, then the image of some larger finitely generated
stage `Spec B₂` is already contained in it. -/
theorem exists_affineAlgebraStageMap_range_subset {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (B₁ : Subalgebra R B) (hB₁ : B₁.FG) (U : (affineBase R B₁).left.Opens)
    (h : Set.range (affineSubalgebraMap B₁).left ⊆ U) :
    ∃ (B₂ : Subalgebra R B) (_ : B₂.FG) (hle : B₁ ≤ B₂),
      Set.range (affineAlgebraStageMap hle).left ⊆ U := by
  obtain ⟨B₂, hB₂, hle, hB₂U⟩ := exists_subalgebra_comap_mem_of_isOpen B₁ hB₁
    (by exact (U : Set (affineBase R B₁).left)) (by exact U.isOpen) (fun p ↦ h ⟨p, rfl⟩)
  refine ⟨B₂, hB₂, hle, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact hB₂U p

/-- Let `P` be a scheme over `Spec R`. Suppose that every morphism over `Spec R` from the
spectrum of an `R`-algebra `C` to `P` factors through the spectrum of a finitely generated
`R`-subalgebra of `C`. Then for every open immersion `j : Spec C ⟶ P`, the ring map
`R → C` underlying `j ≫ P.hom` is of finite type. -/
theorem finiteType_preimage_of_subalgebraFactorization {R : Type u} [CommRing R]
    (P : Over (Spec (CommRingCat.of R)))
    (H : ∀ (C : Type u) [CommRing C] [Algebra R C] (x : affineBase R C ⟶ P),
      ∃ (C₁ : Subalgebra R C) (_ : C₁.FG) (y : affineBase R C₁ ⟶ P),
        affineSubalgebraMap C₁ ≫ y = x)
    (C : Type u) [CommRing C] (j : Spec (CommRingCat.of C) ⟶ P.left) [IsOpenImmersion j] :
    (Spec.preimage (j ≫ P.hom)).hom.FiniteType := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of C := Spec.preimage (j ≫ P.hom)
  have hφ : Spec.map φ = j ≫ P.hom := Spec.map_preimage _
  let _ : Algebra R C := φ.hom.toAlgebra
  let x : affineBase R C ⟶ P := Over.homMk j hφ.symm
  obtain ⟨C₁, hC₁, y, hy⟩ := H C x
  let U : (affineBase R C₁).left.Opens := y.left ⁻¹ᵁ j.opensRange
  have hU : Set.range (affineSubalgebraMap C₁).left ⊆ U := by
    rintro _ ⟨p, rfl⟩
    change y.left ((affineSubalgebraMap C₁).left p) ∈ Set.range j
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hy]
    exact ⟨p, rfl⟩
  obtain ⟨C₂, hC₂, hle, hC₂U⟩ := exists_affineAlgebraStageMap_range_subset C₁ hC₁ U hU
  let y₂ : Spec (CommRingCat.of C₂) ⟶ P.left := (affineAlgebraStageMap hle ≫ y).left
  have hy₂ : Set.range y₂ ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    exact hC₂U ⟨p, rfl⟩
  let g : Spec (CommRingCat.of C₂) ⟶ Spec (CommRingCat.of C) := IsOpenImmersion.lift j y₂ hy₂
  have key : Spec.map (CommRingCat.ofHom (algebraMap C₂ C)) ≫ g =
      𝟙 (Spec (CommRingCat.of C)) := by
    rw [← cancel_mono j, Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp]
    change ((affineSubalgebraMap C₂ ≫ affineAlgebraStageMap hle) ≫ y).left = j
    rw [affineAlgebraStageMap_restrict, hy]
    rfl
  have hsec : Spec.preimage g ≫ CommRingCat.ofHom (algebraMap C₂ C) =
      𝟙 (CommRingCat.of C) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact key
  have hmem : ∀ c : C, c ∈ C₂ := by
    intro c
    have hc := congrArg (fun f ↦ f.hom c) hsec
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      CommRingCat.hom_id, RingHom.id_apply] at hc
    rw [← hc]
    exact ((Spec.preimage g).hom c).property
  have htop : C₂ = ⊤ := eq_top_iff.mpr fun c _ ↦ hmem c
  exact ⟨htop ▸ hC₂⟩

/-- Let `P` be a scheme over `Spec R`. Suppose that every morphism over `Spec R` from the
spectrum of an `R`-algebra `C` to `P` factors through the spectrum of a finitely generated
`R`-subalgebra of `C`. Then the structure morphism of `P` is locally of finite type. -/
theorem locallyOfFiniteType_of_subalgebraFactorization {R : Type u} [CommRing R]
    (P : Over (Spec (CommRingCat.of R)))
    (H : ∀ (C : Type u) [CommRing C] [Algebra R C] (x : affineBase R C ⟶ P),
      ∃ (C₁ : Subalgebra R C) (_ : C₁.FG) (y : affineBase R C₁ ⟶ P),
        affineSubalgebraMap C₁ ≫ y = x) :
    LocallyOfFiniteType P.hom := by
  let 𝒰 := P.left.affineOpenCover
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) 𝒰.openCover
    (fun i ↦ ?_)
  have hft := @finiteType_preimage_of_subalgebraFactorization R _ P H (𝒰.X i) _ (𝒰.f i)
    (𝒰.map_prop i)
  change LocallyOfFiniteType (𝒰.f i ≫ P.hom)
  rw [← Spec.map_preimage (𝒰.f i ≫ P.hom)]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft

/-- Over a noetherian ring, the factorization property of
`locallyOfFiniteType_of_subalgebraFactorization` gives local finite presentation. -/
theorem locallyOfFinitePresentation_of_subalgebraFactorization {R : Type u} [CommRing R]
    [IsNoetherianRing R] (P : Over (Spec (CommRingCat.of R)))
    (H : ∀ (C : Type u) [CommRing C] [Algebra R C] (x : affineBase R C ⟶ P),
      ∃ (C₁ : Subalgebra R C) (_ : C₁.FG) (y : affineBase R C₁ ⟶ P),
        affineSubalgebraMap C₁ ≫ y = x) :
    LocallyOfFinitePresentation P.hom := by
  have := locallyOfFiniteType_of_subalgebraFactorization P H
  infer_instance

end Langlands.AlgebraicGeometry
