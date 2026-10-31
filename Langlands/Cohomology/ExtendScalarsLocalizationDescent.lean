import Langlands.Cohomology.PerfectModuleComplexHomotopy
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Morphisms of scalar extensions to a localization -/

universe u

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

/-- Ordinary scalar extension carries the `R`-scalar multiple of a morphism to
the corresponding scalar multiple of its extension. -/
lemma extendScalars_map_smul {A : Type u} [CommRing A] (φ : R →+* A)
    {M N : ModuleCat.{u} R} (r : R) (v : M ⟶ N) :
    (ModuleCat.extendScalars φ).map (r • v) = φ r • (ModuleCat.extendScalars φ).map v := by
  let := φ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : A) ⊗ₜ[R] (r • v.hom m) = φ r • ((1 : A) ⊗ₜ[R] v.hom m)
  rw [TensorProduct.tmul_smul]
  exact (algebraMap_smul A r _).symm

/-- A morphism between scalar extensions, to a localization, of a finitely
presented module becomes the extension of a morphism over `R` after
multiplication by an element of the submonoid. -/
lemma exists_extendScalars_map_eq_smul_of_isLocalizationMap {A : Type u} [CommRing A]
    (φ : R →+* A) {T : Submonoid R} (hT : T.IsLocalizationMap φ)
    {M N : ModuleCat.{u} R} [Module.FinitePresentation R M]
    (g : (ModuleCat.extendScalars φ).obj M ⟶ (ModuleCat.extendScalars φ).obj N) :
    ∃ t ∈ T, ∃ v : M ⟶ N, (ModuleCat.extendScalars φ).map v = φ t • g := by
  let := φ.toAlgebra
  have : IsLocalization T A := ⟨hT⟩
  let f : N →ₗ[R] A ⊗[R] N := TensorProduct.mk R A N 1
  have : IsLocalizedModule T f :=
    (isLocalizedModule_iff_isBaseChange T A f).2 (TensorProduct.isBaseChange R N A)
  let g₀ : A ⊗[R] M →ₗ[A] A ⊗[R] N := g.hom
  let g' : M →ₗ[R] A ⊗[R] N := g₀.restrictScalars R ∘ₗ TensorProduct.mk R A M 1
  obtain ⟨v, t, hv⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule T f g'
  refine ⟨t, t.2, ModuleCat.ofHom v, ?_⟩
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have hm := LinearMap.congr_fun hv m
  change (1 : A) ⊗ₜ[R] v m = φ t • g₀ ((1 : A) ⊗ₜ[R] m)
  exact hm.trans (algebraMap_smul A (t : R) _).symm

/-- Two morphisms from a finite module whose extensions to a localization agree
already agree after multiplication by an element of the submonoid. -/
lemma exists_smul_eq_of_extendScalars_map_eq_of_isLocalizationMap {A : Type u}
    [CommRing A] (φ : R →+* A) {T : Submonoid R} (hT : T.IsLocalizationMap φ)
    {M N : ModuleCat.{u} R} [Module.Finite R M] (v w : M ⟶ N)
    (h : (ModuleCat.extendScalars φ).map v = (ModuleCat.extendScalars φ).map w) :
    ∃ t ∈ T, t • v = t • w := by
  let := φ.toAlgebra
  have : IsLocalization T A := ⟨hT⟩
  let f : N →ₗ[R] A ⊗[R] N := TensorProduct.mk R A N 1
  have : IsLocalizedModule T f :=
    (isLocalizedModule_iff_isBaseChange T A f).2 (TensorProduct.isBaseChange R N A)
  have hfw : f ∘ₗ v.hom = f ∘ₗ w.hom := by
    ext m
    have := congrArg (fun k ↦ k.hom ((1 : A) ⊗ₜ[R, φ] m)) h
    exact this
  obtain ⟨t, ht⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule T f v.hom w.hom hfw
  refine ⟨t, t.2, ?_⟩
  ext m
  exact LinearMap.congr_fun ht m

/-- If a morphism over the target becomes an extension of scalars after
multiplication by `φ s`, the same holds after multiplication by `φ (t * s)`. -/
lemma exists_extendScalars_map_eq_smul_mul {A : Type u} [CommRing A] (φ : R →+* A)
    {M N : ModuleCat.{u} R}
    {g : (ModuleCat.extendScalars φ).obj M ⟶ (ModuleCat.extendScalars φ).obj N} {s : R} (t : R)
    (h : ∃ v : M ⟶ N, (ModuleCat.extendScalars φ).map v = φ s • g) :
    ∃ v : M ⟶ N, (ModuleCat.extendScalars φ).map v = φ (t * s) • g := by
  obtain ⟨v, hv⟩ := h
  exact ⟨t • v, by rw [extendScalars_map_smul, hv, smul_smul, map_mul]⟩

/-- If a morphism over the target becomes an extension of scalars after
multiplication by `φ s`, the same holds after multiplication by `φ s'` for every
multiple `s'` of `s`. -/
lemma exists_extendScalars_map_eq_smul_of_dvd {A : Type u} [CommRing A] (φ : R →+* A)
    {M N : ModuleCat.{u} R}
    {g : (ModuleCat.extendScalars φ).obj M ⟶ (ModuleCat.extendScalars φ).obj N} {s s' : R}
    (hss' : s ∣ s') (h : ∃ v : M ⟶ N, (ModuleCat.extendScalars φ).map v = φ s • g) :
    ∃ v : M ⟶ N, (ModuleCat.extendScalars φ).map v = φ s' • g := by
  obtain ⟨t, rfl⟩ := hss'
  rw [mul_comm]
  exact exists_extendScalars_map_eq_smul_mul φ t h

/-- Two morphisms over `R` agreeing after multiplication by an element whose
image is a unit have equal scalar extensions. -/
lemma extendScalars_map_eq_of_smul_eq {A : Type u} [CommRing A] (φ : R →+* A)
    {M N : ModuleCat.{u} R} {t : R} (ht : IsUnit (φ t)) {v w : M ⟶ N} (h : t • v = t • w) :
    (ModuleCat.extendScalars φ).map v = (ModuleCat.extendScalars φ).map w := by
  have h' := congrArg (ModuleCat.extendScalars φ).map h
  rw [extendScalars_map_smul, extendScalars_map_smul] at h'
  exact ht.smul_left_cancel.1 h'

/-- A family of properties of elements of `R`, each stable under multiplication,
trivial outside a finite set and realized inside the submonoid `T` at every index
of that set, is realized by one common element of `T`. -/
lemma exists_mem_forall_of_finset {ι : Type*} (T : Submonoid R) (Q : ι → R → Prop)
    (hQ : ∀ i x y, Q i x → Q i (y * x)) (s : Finset ι) (hs : ∀ i ∉ s, ∀ x, Q i x)
    (h : ∀ i ∈ s, ∃ x ∈ T, Q i x) : ∃ x ∈ T, ∀ i, Q i x := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, ∃ x ∈ T, Q i x) → ∃ x ∈ T, ∀ i ∈ s, Q i x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨1, T.one_mem, by simp⟩
    | insert a s _ ih =>
      intro h'
      obtain ⟨x, hx, hxs⟩ := ih fun i hi ↦ h' i (Finset.mem_insert_of_mem hi)
      obtain ⟨y, hy, hya⟩ := h' a (Finset.mem_insert_self a s)
      refine ⟨y * x, T.mul_mem hy hx, fun i hi ↦ ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [mul_comm]
        exact hQ i y x hya
      · exact hQ i x y (hxs i hi)
  obtain ⟨x, hx, hxs⟩ := key s h
  exact ⟨x, hx, fun i ↦ if hi : i ∈ s then hxs i hi else hs i hi x⟩

/-- Finitely many morphisms between scalar extensions to a localization, with all
other members of the family between zero modules, become extensions of
morphisms over `R` after multiplication by one common element of the submonoid. -/
lemma exists_mem_forall_extendScalars_map_eq_smul {A : Type u} [CommRing A]
    (φ : R →+* A) {T : Submonoid R} (hT : T.IsLocalizationMap φ) {ι : Type*} (s : Finset ι)
    (M N : ι → ModuleCat.{u} R) [∀ i, Module.FinitePresentation R (M i)]
    (g : ∀ i, (ModuleCat.extendScalars φ).obj (M i) ⟶ (ModuleCat.extendScalars φ).obj (N i))
    (hs : ∀ i ∉ s, IsZero (M i) ∨ IsZero (N i)) :
    ∃ t ∈ T, ∀ i, ∃ v : M i ⟶ N i, (ModuleCat.extendScalars φ).map v = φ t • g i := by
  refine exists_mem_forall_of_finset T _
    (fun i x y h ↦ exists_extendScalars_map_eq_smul_mul φ y h) s (fun i hi x ↦ ⟨0, ?_⟩)
    (fun i _ ↦ exists_extendScalars_map_eq_smul_of_isLocalizationMap φ hT (g i))
  rcases hs i hi with h | h
  · exact ((ModuleCat.extendScalars φ).map_isZero h).eq_of_src _ _
  · exact ((ModuleCat.extendScalars φ).map_isZero h).eq_of_tgt _ _

/-- The doubly indexed form of `exists_mem_forall_extendScalars_map_eq_smul`:
morphisms `g i j` between scalar extensions of two families of finitely
presented modules, both zero outside a finite set, become extensions of
morphisms over `R` after multiplication by one common element of the
submonoid. -/
lemma exists_mem_forall₂_extendScalars_map_eq_smul {A : Type u} [CommRing A]
    (φ : R →+* A) {T : Submonoid R} (hT : T.IsLocalizationMap φ) {ι : Type*} (s : Finset ι)
    (M N : ι → ModuleCat.{u} R) [∀ i, Module.FinitePresentation R (M i)]
    (g : ∀ i j, (ModuleCat.extendScalars φ).obj (M i) ⟶ (ModuleCat.extendScalars φ).obj (N j))
    (hs : ∀ i ∉ s, IsZero (M i) ∧ IsZero (N i)) :
    ∃ t ∈ T, ∀ i j, ∃ v : M i ⟶ N j, (ModuleCat.extendScalars φ).map v = φ t • g i j := by
  obtain ⟨t, ht, h⟩ := exists_mem_forall_extendScalars_map_eq_smul φ hT (s ×ˢ s)
    (fun ij : ι × ι ↦ M ij.1) (fun ij ↦ N ij.2) (fun ij ↦ g ij.1 ij.2) (fun ij hij ↦ by
      rw [Finset.mem_product, not_and_or] at hij
      exact hij.imp (fun h ↦ (hs _ h).1) (fun h ↦ (hs _ h).2))
  exact ⟨t, ht, fun i j ↦ h (i, j)⟩

/-- Finitely many pairs of morphisms from finite modules, with equal scalar
extensions to a localization and with all other members of the family defined
on zero modules, agree after multiplication by one common element of the
submonoid. -/
lemma exists_mem_forall_smul_eq_of_extendScalars_map_eq {A : Type u} [CommRing A]
    (φ : R →+* A) {T : Submonoid R} (hT : T.IsLocalizationMap φ) {ι : Type*} (s : Finset ι)
    (M N : ι → ModuleCat.{u} R) [∀ i, Module.Finite R (M i)] (v w : ∀ i, M i ⟶ N i)
    (h : ∀ i, (ModuleCat.extendScalars φ).map (v i) = (ModuleCat.extendScalars φ).map (w i))
    (hs : ∀ i ∉ s, IsZero (M i)) :
    ∃ t ∈ T, ∀ i, t • v i = t • w i :=
  exists_mem_forall_of_finset T (fun i t ↦ t • v i = t • w i)
    (fun i x y h ↦ by simp only [mul_smul, h]) s (fun i hi x ↦ (hs i hi).eq_of_src _ _)
    (fun i _ ↦ exists_smul_eq_of_extendScalars_map_eq_of_isLocalizationMap φ hT (v i) (w i) (h i))

/-- Extension of scalars of the standard free module of rank `n` is free of
rank `n`. -/
lemma nonempty_extendScalars_pi_equiv {A : Type u} [CommRing A] (φ : R →+* A) (n : ℕ) :
    Nonempty ((ModuleCat.extendScalars φ).obj (ModuleCat.of R (Fin n → R)) ≃ₗ[A]
      (Fin n → A)) := by
  let := φ.toAlgebra
  exact ⟨TensorProduct.piScalarRight R A A (Fin n)⟩

end Langlands.Cohomology.ModuleComplex
