/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Functorial objectwise injective resolutions -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Remove the constant summand J(0), without assuming that J is additive.
private def normalized (J : C ⥤ C) : C ⥤ C where
  obj A := kernel (J.map (0 : A ⟶ 0))
  map {A B} f := kernel.map _ _ (J.map f) (𝟙 _) (by simp [← J.map_comp])
  map_id A := by
    apply (cancel_mono (kernel.ι _)).1
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp [J.map_comp]

private def normalizedUnit (J : C ⥤ C) (η : 𝟭 C ⟶ J) :
    𝟭 C ⟶ normalized J where
  app A := kernel.lift _ (η.app A) (by simpa using (η.naturality (0 : A ⟶ 0)).symm)
  naturality {A B} f := by
    apply (cancel_mono (kernel.ι _)).1
    simpa [normalized] using η.naturality f

private lemma normalized_mono (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A, Mono (η.app A)) (A : C) : Mono ((normalizedUnit J η).app A) := by
  have := hη A
  dsimp [normalizedUnit]
  infer_instance

private theorem normalized_preservesZero (J : C ⥤ C) :
    (normalized J).PreservesZeroMorphisms where
  map_zero A B := by
    apply (cancel_mono (kernel.ι _)).1
    dsimp [normalized]
    simp only [kernel.lift_ι, zero_comp]
    have h : (0 : A ⟶ B) = (0 : A ⟶ 0) ≫ (0 : 0 ⟶ B) := by simp
    rw [h, J.map_comp, ← Category.assoc, kernel.condition, zero_comp]

attribute [local instance] normalized_preservesZero

private lemma normalized_injective (J : C ⥤ C)
    (hJ : ∀ A, Injective (J.obj A)) (A : C) : Injective ((normalized J).obj A) := by
  let p := J.map (0 : A ⟶ (0 : C))
  let s := J.map (0 : (0 : C) ⟶ A)
  have hs : s ≫ p = 𝟙 _ := by
    dsimp [s, p]
    rw [← J.map_comp]
    have h : (0 : (0 : C) ⟶ A) ≫ (0 : A ⟶ 0) = 𝟙 _ :=
      (isZero_zero C).eq_of_tgt _ _
    rw [h, J.map_id]
  let r : J.obj A ⟶ kernel p := kernel.lift p (𝟙 _ - p ≫ s) (by
    simp [Preadditive.sub_comp, Category.assoc, hs])
  have hr : kernel.ι p ≫ r = 𝟙 _ := by
    apply (cancel_mono (kernel.ι p)).1
    simp [r, Preadditive.comp_sub]
  have := hJ A
  exact (show Retract (kernel p) (J.obj A) from
    { i := kernel.ι p, r := r, retract := hr }).injective

-- The functorial quotient of each monomorphic embedding.
private def quotientStep (K : C ⥤ C) (ι : 𝟭 C ⟶ K) : C ⥤ C where
  obj A := cokernel (ι.app A)
  map {A B} f := cokernel.map _ _ f (K.map f) (ι.naturality f).symm
  map_id A := by
    apply (cancel_epi (cokernel.π _)).1
    simp
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).1
    simp [K.map_comp]

private theorem quotientStep_preservesZero (K : C ⥤ C) (ι : 𝟭 C ⟶ K)
    [K.PreservesZeroMorphisms] : (quotientStep K ι).PreservesZeroMorphisms where
  map_zero A B := by
    apply (cancel_epi (cokernel.π _)).1
    simp [quotientStep]

attribute [local instance] quotientStep_preservesZero

-- Q₀(A) = A and Qₙ₊₁(A) = coker(Qₙ(A) → K(Qₙ(A))).
private def syzygy (K : C ⥤ C) (ι : 𝟭 C ⟶ K) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => syzygy K ι n ⋙ quotientStep K ι

-- The resolution term is K(Qₙ(A)); its differential factors through Qₙ₊₁(A).
private def degree (K : C ⥤ C) (ι : 𝟭 C ⟶ K) (n : ℕ) : C ⥤ C :=
  syzygy K ι n ⋙ K

set_option backward.isDefEq.respectTransparency false in
private def differential (K : C ⥤ C) (ι : 𝟭 C ⟶ K) (n : ℕ) :
    degree K ι n ⟶ degree K ι (n + 1) where
  app A := cokernel.π (ι.app ((syzygy K ι n).obj A)) ≫
    ι.app ((quotientStep K ι).obj ((syzygy K ι n).obj A))
  naturality {A B} f := by
    dsimp [degree, syzygy]
    simp only [Category.assoc]
    rw [← ι.naturality]
    simp [quotientStep]

private lemma differential_sq (K : C ⥤ C) (ι : 𝟭 C ⟶ K) (n : ℕ) (A : C) :
    (differential K ι n).app A ≫ (differential K ι (n + 1)).app A = 0 := by
  simp [differential, degree, syzygy]

private def objectResolution (K : C ⥤ C) (ι : 𝟭 C ⟶ K) : C ⥤ CochainComplex C ℕ where
  obj A := CochainComplex.of (fun n ↦ (degree K ι n).obj A)
    (fun n ↦ (differential K ι n).app A) (fun n ↦ differential_sq K ι n A)
  map f := CochainComplex.ofHom (fun n ↦ (degree K ι n).map f) (fun n ↦ by
    simp only [of_d]
    exact (differential K ι n).naturality f)
  map_id A := by ext n; exact (degree K ι n).map_id A
  map_comp f g := by ext n; exact (degree K ι n).map_comp f g

set_option backward.defeqAttrib.useBackward true in
private def objectAugmentation (K : C ⥤ C) (ι : 𝟭 C ⟶ K) :
    single₀ C ⟶ objectResolution K ι where
  app A := (fromSingle₀Equiv _ _).symm ⟨ι.app A, by
    simp [objectResolution, CochainComplex.of.d, differential, syzygy]⟩
  naturality {A B} f := by
    ext
    simpa [objectResolution, degree, syzygy, fromSingle₀Equiv] using ι.naturality f

private theorem syzygy_preservesZero (K : C ⥤ C) (ι : 𝟭 C ⟶ K)
    [K.PreservesZeroMorphisms] (n : ℕ) : (syzygy K ι n).PreservesZeroMorphisms := by
  induction n with
  | zero => dsimp [syzygy]; infer_instance
  | succ n ih => dsimp [syzygy]; infer_instance

attribute [local instance] syzygy_preservesZero

private theorem degree_preservesZero (K : C ⥤ C) (ι : 𝟭 C ⟶ K)
    [K.PreservesZeroMorphisms] (n : ℕ) : (degree K ι n).PreservesZeroMorphisms := by
  dsimp [degree]
  infer_instance

attribute [local instance] degree_preservesZero

private theorem objectResolution_preservesZero (K : C ⥤ C) (ι : 𝟭 C ⟶ K)
    [K.PreservesZeroMorphisms] : (objectResolution K ι).PreservesZeroMorphisms where
  map_zero A B := by
    ext n
    exact (degree K ι n).map_zero A B

attribute [local instance] objectResolution_preservesZero

-- Postcomposing a cokernel differential with a mono preserves exactness.
private lemma exact_cokernel_comp {X Y Z : C} (f : X ⟶ Y)
    (g : cokernel f ⟶ Z) [Mono g] :
    (ShortComplex.mk f (cokernel.π f ≫ g) (by simp)).Exact := by
  let φ : ShortComplex.mk f (cokernel.π f) (by simp) ⟶
      ShortComplex.mk f (cokernel.π f ≫ g) (by simp) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := g }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (ShortComplex.exact_cokernel f)

private lemma objectResolution_exact_succ (K : C ⥤ C) (ι : 𝟭 C ⟶ K)
    (hι : ∀ A, Mono (ι.app A)) (A : C) (n : ℕ) :
    ((objectResolution K ι).obj A).ExactAt (n + 1) := by
  have := hι ((syzygy K ι (n + 1)).obj A)
  have := hι ((syzygy K ι (n + 2)).obj A)
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  let S := ShortComplex.mk (ι.app ((syzygy K ι (n + 1)).obj A))
    ((differential K ι (n + 1)).app A) (by simp [differential])
  have hS : S.Exact := exact_cokernel_comp _ _
  -- Precomposing the preceding embedding with the quotient epi preserves exactness.
  let T := ((objectResolution K ι).obj A).sc' n (n + 1) (n + 1 + 1)
  let φ : T ⟶ S :=
    { τ₁ := cokernel.π (ι.app ((syzygy K ι n).obj A))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, S, objectResolution, differential, CochainComplex.of.d, syzygy]
      comm₂₃ := by simp [T, S, objectResolution, CochainComplex.of.d] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma objectAugmentation_quasiIso (K : C ⥤ C) (ι : 𝟭 C ⟶ K)
    (hι : ∀ A, Mono (ι.app A)) (A : C) :
    QuasiIso ((objectAugmentation K ι).app A) := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · constructor
      · simpa [objectAugmentation, objectResolution, CochainComplex.of.d,
          differential, degree, syzygy, fromSingle₀Equiv] using
          (exact_cokernel_comp (ι.app A) (ι.app ((quotientStep K ι).obj A)))
      · simpa [objectAugmentation] using hι A
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact objectResolution_exact_succ K ι hι A n
    · exact CochainComplex.exactAt_succ_single_obj _ _

/-- A functorial injective resolution of objects, indexed in nonnegative degrees.

Source: Stacks Project, Derived Categories, Tag 0141, construction preceding assertion (1).
(auxiliary; not a blueprint node).

The construction first replaces the given embedding by its kernel over the zero object,
so that the resulting functor preserves the zero object and zero morphisms.  It then iterates
cokernels of the successive monomorphic embeddings.  Kernel and cokernel universal
properties make all maps functorial, while the retract argument preserves injectivity.
The augmented nonnegative complexes are exact by the kernel--cokernel identities.
-/
theorem exists_functorial_object_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A : C, Mono (η.app A)) (hJ : ∀ A : C, Injective (J.obj A)) :
    ∃ (E : C ⥤ CochainComplex C ℕ)
      (ε : (CochainComplex.single₀ C) ⟶ E),
      (∀ A : C, QuasiIso (ε.app A)) ∧
      (∀ (A B : C), E.map (0 : A ⟶ B) = 0) ∧
      IsZero (E.obj (0 : C)) ∧
      (∀ (A : C) (n : ℕ), Injective ((E.obj A).X n)) := by
  let K := normalized J
  let ι := normalizedUnit J η
  have hι : ∀ A, Mono (ι.app A) := normalized_mono J η hη
  let E := objectResolution K ι
  refine ⟨E, objectAugmentation K ι, objectAugmentation_quasiIso K ι hι,
    fun A B ↦ E.map_zero A B, ?_, ?_⟩
  · rw [IsZero.iff_id_eq_zero, ← E.map_id]
    rw [(isZero_zero C).eq_of_src (𝟙 (0 : C)) 0, E.map_zero]
  · intro A n
    exact normalized_injective J hJ ((syzygy K ι n).obj A)

end

end CochainComplex
