import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.FinitePresentation

/-! # Local finite presentation from factorizations through finitely presented quotients

Let `P` be a scheme locally of finite type over `Spec R`. Suppose that every morphism over
`Spec R` from `Spec (D ⧸ I)` to `P`, for an `R`-algebra `D` and an ideal `I`, factors through
`Spec (D ⧸ J)` for a finitely generated ideal `J ≤ I`. Then `P` is locally of finite
presentation over `Spec R`. The proof is a retract argument on affine opens.
-/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

open Langlands.AlgebraicGeometry.Picard

variable {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]

/-- The affine-base arrow `Spec (D ⧸ I) ⟶ Spec (D ⧸ J)` induced by an inclusion `J ≤ I`. -/
def affineQuotientMap {I J : Ideal D} (h : J ≤ I) :
    affineBase R (D ⧸ I) ⟶ affineBase R (D ⧸ J) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) (by
    dsimp only [affineBase, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)

@[reassoc]
lemma affineQuotientMap_comp {I J K : Ideal D} (hJI : J ≤ I) (hKJ : K ≤ J) :
    (affineQuotientMap (R := R) hJI) ≫ affineQuotientMap hKJ =
      affineQuotientMap (hKJ.trans hJI) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp]

/-- Let `J ≤ I` be ideals of `D`, and let `U` be an open subset of `Spec (D ⧸ J)` containing
the image of `Spec (D ⧸ I)`. Then for some finitely generated ideal `J'` with `J ≤ J' ≤ I`, the
image of `Spec (D ⧸ J')` is contained in `U`; `J'` is `J` plus one element of `I`. -/
theorem exists_quotient_comap_mem_of_isOpen {I J : Ideal D} (hJ : J.FG) (hJI : J ≤ I)
    (U : Set (PrimeSpectrum (D ⧸ J))) (hU : IsOpen U)
    (h : ∀ p : PrimeSpectrum (D ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.factor hJI) p ∈ U) :
    ∃ (J' : Ideal D) (_ : J'.FG) (hJJ' : J ≤ J') (_ : J' ≤ I),
      ∀ p : PrimeSpectrum (D ⧸ J'),
        PrimeSpectrum.comap (Ideal.Quotient.factor hJJ') p ∈ U := by
  obtain ⟨K, hK⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).mp hU.isClosed_compl
  have htop : K.map (Ideal.Quotient.factor hJI) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hp := h ⟨m, hm.isPrime⟩
    have hc : PrimeSpectrum.comap (Ideal.Quotient.factor hJI) ⟨m, hm.isPrime⟩ ∈ Uᶜ := by
      rw [hK, PrimeSpectrum.mem_zeroLocus]
      intro x hx
      exact hle (Ideal.mem_map_of_mem _ hx)
    exact hc hp
  have hsurj : Function.Surjective (Ideal.Quotient.factor hJI) :=
    Ideal.Quotient.factor_surjective hJI
  have h1 : (1 : D ⧸ I) ∈ K.map (Ideal.Quotient.factor hJI) := by
    rw [htop]
    trivial
  rw [Ideal.mem_map_iff_of_surjective _ hsurj] at h1
  obtain ⟨k, hkK, hk1⟩ := h1
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective k
  have hd : 1 - d ∈ I := by
    rw [← Ideal.Quotient.eq]
    rw [Ideal.Quotient.factor_mk] at hk1
    rw [hk1, map_one]
  refine ⟨J ⊔ Ideal.span {1 - d}, Submodule.FG.sup hJ (Submodule.fg_span_singleton _),
    le_sup_left, sup_le hJI ((Ideal.span_singleton_le_iff_mem _).mpr hd), fun p ↦ ?_⟩
  by_contra hp
  have hp' : PrimeSpectrum.comap (Ideal.Quotient.factor
      (le_sup_left : J ≤ J ⊔ Ideal.span {1 - d})) p ∈ Uᶜ := hp
  rw [hK, PrimeSpectrum.mem_zeroLocus] at hp'
  have hmem : Ideal.Quotient.mk (J ⊔ Ideal.span {1 - d}) d ∈ p.asIdeal := hp' hkK
  have hone : Ideal.Quotient.mk (J ⊔ Ideal.span {1 - d}) d = 1 := by
    rw [← map_one (Ideal.Quotient.mk (J ⊔ Ideal.span {1 - d})), Ideal.Quotient.eq]
    have : d - 1 = -(1 - d) := by ring
    rw [this]
    exact neg_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hone ▸ hmem))

/-- Scheme form of `exists_quotient_comap_mem_of_isOpen`. -/
theorem exists_affineQuotientMap_range_subset {I J : Ideal D} (hJ : J.FG) (hJI : J ≤ I)
    (U : (affineBase R (D ⧸ J)).left.Opens)
    (h : Set.range (affineQuotientMap (R := R) hJI).left ⊆ U) :
    ∃ (J' : Ideal D) (_ : J'.FG) (hJJ' : J ≤ J') (_ : J' ≤ I),
      Set.range (affineQuotientMap (R := R) hJJ').left ⊆ U := by
  obtain ⟨J', hJ', hJJ', hJ'I, hJ'U⟩ := exists_quotient_comap_mem_of_isOpen hJ hJI
    (by exact (U : Set (affineBase R (D ⧸ J)).left)) (by exact U.isOpen) (fun p ↦ h ⟨p, rfl⟩)
  refine ⟨J', hJ', hJJ', hJ'I, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact hJ'U p

/-- The factorization hypothesis of the finite-presentation criterion: every morphism over
`Spec R` from `Spec (D ⧸ I)` to `P` factors through `Spec (D ⧸ J)` for a finitely generated
ideal `J ≤ I`. -/
def HasQuotientFactorization {R : Type u} [CommRing R] (P : Over (Spec (CommRingCat.of R))) :
    Prop :=
  ∀ (D : Type u) [CommRing D] [Algebra R D] (I : Ideal D) (x : affineBase R (D ⧸ I) ⟶ P),
    ∃ (J : Ideal D) (_ : J.FG) (hJ : J ≤ I) (y : affineBase R (D ⧸ J) ⟶ P),
      affineQuotientMap hJ ≫ y = x

/-- Let `P` be a scheme over `Spec R` with the quotient factorization property. Then for every
open immersion `j : Spec C ⟶ P` such that `R → C` is of finite type, `R → C` is of finite
presentation. -/
theorem finitePresentation_preimage_of_quotientFactorization {R : Type u} [CommRing R]
    (P : Over (Spec (CommRingCat.of R))) (H : HasQuotientFactorization P)
    (C : Type u) [CommRing C] (j : Spec (CommRingCat.of C) ⟶ P.left) [IsOpenImmersion j]
    (hft : (Spec.preimage (j ≫ P.hom)).hom.FiniteType) :
    (Spec.preimage (j ≫ P.hom)).hom.FinitePresentation := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of C := Spec.preimage (j ≫ P.hom)
  have hφ : Spec.map φ = j ≫ P.hom := Spec.map_preimage _
  let _ : Algebra R C := φ.hom.toAlgebra
  have hft' : Algebra.FiniteType R C := hft
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  let D := MvPolynomial (Fin n) R
  let I : Ideal D := RingHom.ker π
  let e : (D ⧸ I) ≃ₐ[R] C := Ideal.quotientKerAlgEquivOfSurjective hπ
  have he : Spec.map (CommRingCat.ofHom (e.symm : C →+* D ⧸ I)) ≫ Spec.map φ =
      (affineBase R (D ⧸ I)).hom := by
    dsimp only [affineBase, Over.mk_hom]
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact e.symm.commutes r
  let x : affineBase R (D ⧸ I) ⟶ P :=
    Over.homMk (Spec.map (CommRingCat.ofHom (e.symm : C →+* D ⧸ I)) ≫ j)
      (by
        have h := he
        rw [hφ] at h
        exact (Category.assoc _ _ _).trans h)
  obtain ⟨J, hJfg, hJ, y, hy⟩ := H D I x
  let U : (affineBase R (D ⧸ J)).left.Opens := y.left ⁻¹ᵁ j.opensRange
  have hU : Set.range (affineQuotientMap (R := R) hJ).left ⊆ U := by
    rintro _ ⟨p, rfl⟩
    change y.left ((affineQuotientMap hJ).left p) ∈ Set.range j
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hy]
    exact ⟨_, rfl⟩
  obtain ⟨J₂, hJ₂, hJJ₂, hJ₂I, hJ₂U⟩ := exists_affineQuotientMap_range_subset hJfg hJ U hU
  let y₂ : Spec (CommRingCat.of (D ⧸ J₂)) ⟶ P.left := (affineQuotientMap hJJ₂ ≫ y).left
  have hy₂ : Set.range y₂ ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    exact hJ₂U ⟨p, rfl⟩
  let g : Spec (CommRingCat.of (D ⧸ J₂)) ⟶ Spec (CommRingCat.of C) :=
    IsOpenImmersion.lift j y₂ hy₂
  have hgj : g ≫ j = y₂ := IsOpenImmersion.lift_fac _ _ _
  have key : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ₂I)) ≫ g =
      Spec.map (CommRingCat.ofHom (e.symm : C →+* D ⧸ I)) := by
    rw [← cancel_mono j, Category.assoc, hgj]
    change ((affineQuotientMap hJ₂I ≫ affineQuotientMap hJJ₂) ≫ y).left = _
    rw [affineQuotientMap_comp, hy]
    rfl
  -- the ring map `ψ : C → D ⧸ J₂` underlying `g` is a section of `D ⧸ J₂ → D ⧸ I ≃ C`
  let ψ : C →+* D ⧸ J₂ := (Spec.preimage g).hom
  have hψ : (Ideal.Quotient.factor hJ₂I).comp ψ = (e.symm : C →+* D ⧸ I) := by
    have : Spec.preimage g ≫ CommRingCat.ofHom (Ideal.Quotient.factor hJ₂I) =
        CommRingCat.ofHom (e.symm : C →+* D ⧸ I) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact key
    exact congrArg CommRingCat.Hom.hom this
  let ρ : D ⧸ J₂ →+* C := (e : D ⧸ I →+* C).comp (Ideal.Quotient.factor hJ₂I)
  have hρψ : ρ.comp ψ = RingHom.id C := by
    ext c
    change e ((Ideal.Quotient.factor hJ₂I).comp ψ c) = c
    rw [hψ]
    exact e.apply_symm_apply c
  -- `ψ` is a morphism of `R`-algebras
  have hψR : ψ.comp φ.hom = algebraMap R (D ⧸ J₂) := by
    have : φ ≫ Spec.preimage g = CommRingCat.ofHom (algebraMap R (D ⧸ J₂)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, hφ, ← Category.assoc, hgj]
      exact Over.w (affineQuotientMap hJJ₂ ≫ y)
    exact congrArg CommRingCat.Hom.hom this
  have hρR : ρ.comp (algebraMap R (D ⧸ J₂)) = φ.hom := by
    ext r
    change e (algebraMap R (D ⧸ I) r) = algebraMap R C r
    exact e.commutes r
  have hfp : (algebraMap R (D ⧸ J₂)).FinitePresentation := by
    rw [RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.quotient hJ₂
  have hψft : ψ.FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (f := φ.hom)
      (by rw [hψR]; exact RingHom.FiniteType.of_finitePresentation hfp)
  have hρ : ρ.FinitePresentation :=
    RingHom.FinitePresentation.of_comp_finiteType ψ (by rw [hρψ]; exact .id C) hψft
  change φ.hom.FinitePresentation
  rw [← hρR]
  exact hρ.comp hfp

/-- Let `P` be a scheme locally of finite type over `Spec R` with the quotient factorization
property. Then the structure morphism of `P` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_quotientFactorization {R : Type u} [CommRing R]
    (P : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType P.hom]
    (H : HasQuotientFactorization P) :
    LocallyOfFinitePresentation P.hom := by
  let 𝒰 := P.left.affineOpenCover
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) 𝒰.openCover
    (fun i ↦ ?_)
  have hft : (Spec.preimage (𝒰.f i ≫ P.hom)).hom.FiniteType := by
    have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    have := 𝒰.map_prop i
    have h : LocallyOfFiniteType (𝒰.f i ≫ P.hom) :=
      IsZariskiLocalAtSource.comp (P := @LocallyOfFiniteType) inferInstance (𝒰.f i)
    rw [← Spec.map_preimage (𝒰.f i ≫ P.hom)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h
  have hfp := @finitePresentation_preimage_of_quotientFactorization R _ P H (𝒰.X i) _ (𝒰.f i)
    (𝒰.map_prop i) hft
  change LocallyOfFinitePresentation (𝒰.f i ≫ P.hom)
  rw [← Spec.map_preimage (𝒰.f i ≫ P.hom)]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hfp

end Langlands.AlgebraicGeometry

end
