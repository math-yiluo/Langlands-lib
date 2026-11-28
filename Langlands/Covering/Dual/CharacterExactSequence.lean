import Langlands.Topology.ComplexCharacterExtension
import Mathlib.GroupTheory.GroupExtension.Defs

/-! # Algebraic complex characters of a short exact sequence -/

universe u v w

namespace Langlands.Covering.Dual

/-- Algebraic complex characters with pointwise multiplication. -/
abbrev Character (G : Type u) [Monoid G] := G →* ℂˣ

/-- Pull back an algebraic complex character by precomposition. -/
def precompose {G : Type u} {H : Type v} [Monoid G] [Monoid H] (f : G →* H) :
    Character H →* Character G :=
  MonoidHom.compHom' f

@[simp] theorem precompose_apply {G : Type u} {H : Type v} [Monoid G] [Monoid H]
    (f : G →* H) (χ : Character H) : precompose f χ = χ.comp f := rfl

variable {B : Type u} {E : Type v} {D : Type w} [CommGroup B] [CommGroup E] [CommGroup D]

/-- The reversed short exact sequence of complex character groups. -/
def dualExtension (S : GroupExtension B E D) :
    GroupExtension (Character D) (Character E) (Character B) where
  inl := precompose S.rightHom
  rightHom := precompose S.inl
  inl_injective := by
    intro χ ψ h
    apply MonoidHom.ext
    intro d
    obtain ⟨e, rfl⟩ := S.rightHom_surjective d
    exact DFunLike.congr_fun h e
  range_inl_eq_ker_rightHom := by
    apply SetLike.ext
    intro χ
    constructor
    · rintro ⟨ψ, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply MonoidHom.ext
      intro b
      change ψ (S.rightHom (S.inl b)) = 1
      rw [S.rightHom_inl, map_one]
    · intro hχ
      have hker : S.rightHom.ker ≤ χ.ker := by
        intro e he
        rw [← S.range_inl_eq_ker_rightHom] at he
        obtain ⟨b, rfl⟩ := he
        exact DFunLike.congr_fun (MonoidHom.mem_ker.mp hχ) b
      refine ⟨S.rightHom.liftOfSurjective S.rightHom_surjective ⟨χ, hker⟩, ?_⟩
      simpa only [precompose_apply] using
        (S.rightHom.liftOfRightInverse_comp _ _ ⟨χ, hker⟩)
  rightHom_surjective := fun η ↦
    Langlands.Topology.exists_complex_character_extension S.inl S.inl_injective η

@[simp] theorem dualExtension_inl (S : GroupExtension B E D) :
    (dualExtension S).inl = precompose S.rightHom := rfl

@[simp] theorem dualExtension_rightHom (S : GroupExtension B E D) :
    (dualExtension S).rightHom = precompose S.inl := rfl

end Langlands.Covering.Dual
