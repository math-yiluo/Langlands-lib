import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.RegularEpi

universe v u w

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.CategoryTheory.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J (Type w)]

/-- Locally surjective presentations of two sheaves with the same sectionwise
kernel determine an isomorphism compatible with the two presentations. -/
theorem exists_iso_of_isLocallySurjective_of_same_kernel
    {H F G : Sheaf J (Type w)} (a : H ⟶ F) (b : H ⟶ G)
    (ha : Sheaf.IsLocallySurjective a) (hb : Sheaf.IsLocallySurjective b)
    (hker : ∀ (T : Cᵒᵖ) (x y : H.obj.obj T),
      a.hom.app T x = a.hom.app T y ↔ b.hom.app T x = b.hom.app T y) :
    ∃ e : F ≅ G, a ≫ e.hom = b := by
  have : Sheaf.IsLocallySurjective a := ha
  have : Sheaf.IsLocallySurjective b := hb
  have : Epi a := inferInstance
  have : Epi b := inferInstance
  have : IsRegularEpi a := IsRegularEpiCategory.regularEpiOfEpi a
  have : IsRegularEpi b := IsRegularEpiCategory.regularEpiOfEpi b
  have hab : ∀ {Z : Sheaf J (Type w)} (g₁ g₂ : Z ⟶ H),
      g₁ ≫ a = g₂ ≫ a → g₁ ≫ b = g₂ ≫ b := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    apply (hker T (g₁.hom.app T x) (g₂.hom.app T x)).mp
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app ((sheafToPresheaf J (Type w)).congr_map h) T) x
  have hba : ∀ {Z : Sheaf J (Type w)} (g₁ g₂ : Z ⟶ H),
      g₁ ≫ b = g₂ ≫ b → g₁ ≫ a = g₂ ≫ a := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    apply (hker T (g₁.hom.app T x) (g₂.hom.app T x)).mpr
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app ((sheafToPresheaf J (Type w)).congr_map h) T) x
  let f := EffectiveEpi.desc a b hab
  let g := EffectiveEpi.desc b a hba
  have hf : a ≫ f = b := EffectiveEpi.fac a b hab
  have hg : b ≫ g = a := EffectiveEpi.fac b a hba
  exact ⟨{
    hom := f
    inv := g
    hom_inv_id := (cancel_epi a).mp (by simp [← Category.assoc, hf, hg])
    inv_hom_id := (cancel_epi b).mp (by simp [← Category.assoc, hf, hg]) }, hf⟩

end Langlands.CategoryTheory.Sites
