import Langlands.Algebra.ProductLieEnveloping
import Langlands.Global.ComplexEmbeddingLieCoordinates

/-! The actual archimedean enveloping center in the complex embedding coordinates. -/

noncomputable section

open scoped Classical
open NumberField NumberField.InfinitePlace
open Langlands.Algebra Langlands.Algebra.LieEnvelopingEquiv Langlands.Algebra.ProductLieEnveloping
open Langlands.Archimedean.ComplexGenericLarge
open UniversalEnvelopingAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ)

local notation "CP" => {v : InfinitePlace F // IsComplex v}
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "U" => UniversalEnvelopingAlgebra ℂ
local notation "Z" => Subalgebra.center ℂ

/-- The map from an embedding block into the actual complexified archimedean Lie algebra. -/
def complexEmbeddingLieInclusion (j : EmbeddingIndex F) : CM →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  (complexEmbeddingLieCoordinates F n).symm.toLieHom.comp (lieSingle j)

/-- The enveloping map of an embedding block into the actual global enveloping algebra. -/
def complexEmbeddingEnvelopingInclusion (j : EmbeddingIndex F) :
    U CM →ₐ[ℂ] EnvelopingAlgebra F n :=
  LieEnvelopingEquiv.map (complexEmbeddingLieInclusion F n j)

/-- The center of one embedding block maps into the actual global enveloping center. -/
def complexEmbeddingCenterInclusion (j : EmbeddingIndex F) : Z (U CM) →ₐ[ℂ] EnvelopingCenter F n :=
  (Langlands.Algebra.LieEnvelopingEquiv.center
    (enveloping (complexEmbeddingLieCoordinates F n)).symm).toAlgHom.comp (singleCenter j)

@[simp] theorem complexEmbeddingCenterInclusion_val (j : EmbeddingIndex F) (z : Z (U CM)) :
    (complexEmbeddingCenterInclusion F n j z).val =
      complexEmbeddingEnvelopingInclusion F n j z.val := by
  change LieEnvelopingEquiv.map (complexEmbeddingLieCoordinates F n).symm.toLieHom
    (singleEnveloping j z.val) = complexEmbeddingEnvelopingInclusion F n j z.val
  rw [← AlgHom.comp_apply, singleEnveloping, Langlands.Algebra.ProductLieEnveloping.map_comp]
  rfl

/-- The embedding block centers generate the actual global enveloping center. -/
theorem iSup_complexEmbeddingCenterInclusion_range :
    (⨆ j : EmbeddingIndex F, (complexEmbeddingCenterInclusion F n j).range) = ⊤ := by
  let e := Langlands.Algebra.LieEnvelopingEquiv.center
    (enveloping (complexEmbeddingLieCoordinates F n)).symm
  let S : Subalgebra ℂ (EnvelopingCenter F n) :=
    ⨆ j : EmbeddingIndex F, (complexEmbeddingCenterInclusion F n j).range
  have h : (⨆ j : EmbeddingIndex F, (singleCenter (K := ℂ) (L := CM) j).range) ≤
      S.comap e.toAlgHom := by
    apply iSup_le
    intro j
    rintro _ ⟨z, rfl⟩
    exact le_iSup (fun j => (complexEmbeddingCenterInclusion F n j).range) j ⟨z, rfl⟩
  rw [iSup_singleCenter_range] at h
  refine top_unique fun z _ => ?_
  obtain ⟨w, rfl⟩ := e.surjective z
  exact h (show w ∈ (⊤ : Subalgebra ℂ _) by trivial)

/-- Agreement on all block centers determines a map from the actual global center. -/
theorem complexEmbeddingCenter_hom_ext {A : Type*} [Ring A] [Algebra ℂ A]
    (f g : EnvelopingCenter F n →ₐ[ℂ] A)
    (h : ∀ j z, f (complexEmbeddingCenterInclusion F n j z) =
      g (complexEmbeddingCenterInclusion F n j z)) : f = g := by
  have hle : (⨆ j : EmbeddingIndex F, (complexEmbeddingCenterInclusion F n j).range) ≤
      AlgHom.equalizer f g := by
    apply iSup_le
    intro j
    rintro _ ⟨z, rfl⟩
    exact h j z
  rw [iSup_complexEmbeddingCenterInclusion_range] at hle
  exact AlgHom.ext fun z => hle (show z ∈ (⊤ : Subalgebra ℂ _) by trivial)

/-- An embedding Lie inclusion factors through the corresponding actual complex place. -/
theorem complexEmbeddingLieInclusion_place (w : CP) (s : Fin 2) :
    complexEmbeddingLieInclusion F n (complexEmbeddingIndex F (w, s)) =
      (complexPlaceComplexLieInclusion F n w).comp (tensorLieEquiv.symm.toLieHom.comp (lieSingle s)) := by
  apply LieHom.ext
  intro X
  apply (complexEmbeddingLieCoordinates F n).injective
  funext j
  obtain ⟨⟨v, t⟩, rfl⟩ := (complexEmbeddingIndex F).surjective j
  simp only [complexEmbeddingLieInclusion, LieHom.comp_apply, LieEquiv.coe_coe]
  rw [LieEquiv.apply_symm_apply, complexEmbeddingLieCoordinates_apply]
  simp only [lieSingle_apply]
  by_cases h : v = w
  · subst v
    rw [complexPlaceComplexLieProjection_inclusion, LieEquiv.apply_symm_apply]
    by_cases ht : t = s
    · subst t
      simp
    · have hd : complexEmbeddingIndex F (w, t) ≠ complexEmbeddingIndex F (w, s) :=
        fun e => ht (congrArg Prod.snd ((complexEmbeddingIndex F).injective e))
      simp [ht, hd]
  · rw [complexPlaceComplexLieProjection_otherInclusion F n v w h, map_zero]
    have hd : complexEmbeddingIndex F (v, t) ≠ complexEmbeddingIndex F (w, s) :=
      fun e => h (congrArg Prod.fst ((complexEmbeddingIndex F).injective e))
    simp [hd]

/-- The same factorization for the actual enveloping inclusions. -/
theorem complexEmbeddingEnvelopingInclusion_place (w : CP) (s : Fin 2) :
    complexEmbeddingEnvelopingInclusion F n (complexEmbeddingIndex F (w, s)) =
      (complexPlaceEnvelopingInclusion F n w).comp
        (LieEnvelopingEquiv.map (tensorLieEquiv.symm.toLieHom.comp (lieSingle s))) := by
  change LieEnvelopingEquiv.map (complexEmbeddingLieInclusion F n (complexEmbeddingIndex F (w, s))) =
    (LieEnvelopingEquiv.map (complexPlaceComplexLieInclusion F n w)).comp _
  rw [complexEmbeddingLieInclusion_place, Langlands.Algebra.ProductLieEnveloping.map_comp]

end Langlands.Global.ArchimedeanGL
