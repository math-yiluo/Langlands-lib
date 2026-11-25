/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Invertible transposes through mates

Three formal facts on adjunctions used to show that a transpose under an adjunction is
invertible.

* `CategoryTheory.Adjunction.homEquiv_symm_map_comp_app`: the transpose of `G f ≫ β_Y` along
  `L₂ ⊣ R₂`, for a square `β : R₁ ⋙ G ⟶ H ⋙ R₂`, is the mate of `β` followed by `H` of the
  transpose of `f` along `L₁ ⊣ R₁`.
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_of_unit_comp`: if `R₃ ≅ R₂ ⋙ R₁` and
  `t : L₁ M ⟶ R₂ (L₃ M)` is compatible with the units, then the transpose of `t` along
  `L₂ ⊣ R₂` is invertible: it is a component of the comparison `L₁ ⋙ L₂ ≅ L₃` of left adjoints.
* `CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv`: when all four sides of a square are
  left adjoints, a square of right adjoints has invertible left mate as soon as its other mate
  is invertible (iterated mates are conjugates).

Source: Stacks Project, Tag 0GLL (adjunctions, mates and conjugates; Mac Lane, IV.7).
-/

@[expose] public section

namespace CategoryTheory

open Category

section Transpose

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- The transpose of `G f ≫ β_Y` is the mate of `β` followed by `H` of the transpose of `f`.
Proof: apply the hom equivalence of `L₂ ⊣ R₂`; the unit formula of the inverse mate and the
naturality of `β` reduce both sides to `G f ≫ β_Y`. -/
theorem Adjunction.homEquiv_symm_map_comp_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : TwoSquare R₁ H G R₂) {Z : A} {Y : B} (f : Z ⟶ R₁.obj Y) :
    (adj₂.homEquiv _ _).symm (G.map f ≫ β.app Y) =
      ((mateEquiv adj₁ adj₂).symm β).app Z ≫ H.map ((adj₁.homEquiv _ _).symm f) := by
  set g := (adj₁.homEquiv _ _).symm f
  have hf : f = adj₁.unit.app Z ≫ R₁.map g := by
    exact (Equiv.apply_symm_apply _ f).symm.trans (adj₁.homEquiv_unit Z Y g)
  apply (adj₂.homEquiv _ _).injective
  have hn := β.naturality g
  rw [Functor.comp_map, Functor.comp_map] at hn
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, hf, G.map_comp,
    assoc, hn, ← assoc, unit_mateEquiv_symm adj₁ adj₂ β Z, assoc]
  rfl

end Transpose

section LeftAdjointComparison

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : A ⥤ C} {R₃ : C ⥤ A}

/-- Let `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, `L₃ ⊣ R₃` and `e : R₂ ⋙ R₁ ≅ R₃`. If `t : L₁ M ⟶ R₂ (L₃ M)`
satisfies `η₁ ≫ R₁ t = η₃ ≫ e⁻¹`, then the transpose of `t` along `L₂ ⊣ R₂` is invertible.
Proof: it is the component at `M` of the comparison isomorphism `L₁ ⋙ L₂ ≅ L₃` of the left
adjoints of `R₃`, as both have the same transpose along `L₁ ⋙ L₂ ⊣ R₃`. -/
theorem Adjunction.isIso_homEquiv_symm_of_unit_comp (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃) (M : A) (t : L₁.obj M ⟶ R₂.obj (L₃.obj M))
    (ht : adj₁.unit.app M ≫ R₁.map t = adj₃.unit.app M ≫ e.inv.app (L₃.obj M)) :
    IsIso ((adj₂.homEquiv _ _).symm t) := by
  have h : (adj₂.homEquiv _ _).symm t =
      (((adj₁.comp adj₂).ofNatIsoRight e).leftAdjointUniq adj₃).hom.app M := by
    apply (((adj₁.comp adj₂).ofNatIsoRight e).homEquiv _ _).injective
    conv_rhs => rw [Adjunction.homEquiv_unit, Adjunction.unit_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    rw [Adjunction.comp_homEquiv]
    erw [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit, ht]
    simp
  rw [h]
  infer_instance

end LeftAdjointComparison

section IteratedMate

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- If all four sides of a square are left adjoints, a square `β : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂` has
invertible inverse mate `F₁ ⋙ L₂ ⟶ L₁ ⋙ F₂` as soon as its mate `U₂ ⋙ R₁ ⟶ R₂ ⋙ U₁` along
`F₂ ⊣ U₂` and `F₁ ⊣ U₁` is invertible.
Proof: the iterated mate is the conjugate (`iterated_mateEquiv_conjugateEquiv`), and a
transformation of left adjoints with invertible conjugate is invertible. -/
theorem isIso_mateEquiv_symm_of_isIso_mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂) (β : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso (mateEquiv adj₄ adj₃ β)] :
    IsIso ((mateEquiv adj₁ adj₂).symm β) := by
  have h := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄
    ((mateEquiv adj₁ adj₂).symm β)
  rw [Equiv.apply_symm_apply] at h
  have : IsIso (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)
      ((mateEquiv adj₁ adj₂).symm β)) := by
    rw [← h]
    infer_instance
  exact conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) _

end IteratedMate

end CategoryTheory
