/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Morphisms of homology sequences

Let `F : C ⥤ A` be a homological functor from a pretriangulated category to an abelian category,
equipped with a shift sequence. A morphism `φ : T ⟶ T'` of distinguished triangles induces a
morphism between the six-term exact sequences
`F^{n₀}(T₁) ⟶ F^{n₀}(T₂) ⟶ F^{n₀}(T₃) ⟶ F^{n₁}(T₁) ⟶ F^{n₁}(T₂) ⟶ F^{n₁}(T₃)`
(`CategoryTheory.Functor.homologySequenceComposableArrows₅Map`). The four and five lemmas then
control `F^{n₀}(φ.hom₃)` in terms of the other components
(`CategoryTheory.Functor.epi_shift_map_hom₃` and `CategoryTheory.Functor.isIso_shift_map_hom₃`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits Pretriangulated ComposableArrows

variable {C A : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [Category* A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
  {T T' : Triangle C} (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism of six-term homology sequences induced by a morphism of triangles. -/
noncomputable def homologySequenceComposableArrows₅Map :
    F.homologySequenceComposableArrows₅ T n₀ n₁ h ⟶
      F.homologySequenceComposableArrows₅ T' n₀ n₁ h :=
  have w (n : ℤ) : (F.shift n).map T.mor₁ ≫ (F.shift n).map φ.hom₂ =
      (F.shift n).map φ.hom₁ ≫ (F.shift n).map T'.mor₁ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁]
  have w' (n : ℤ) : (F.shift n).map T.mor₂ ≫ (F.shift n).map φ.hom₃ =
      (F.shift n).map φ.hom₂ ≫ (F.shift n).map T'.mor₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
  homMk₅ ((F.shift n₀).map φ.hom₁) ((F.shift n₀).map φ.hom₂) ((F.shift n₀).map φ.hom₃)
    ((F.shift n₁).map φ.hom₁) ((F.shift n₁).map φ.hom₂) ((F.shift n₁).map φ.hom₃)
    (w n₀) (w' n₀) (F.homologySequenceδ_naturality φ n₀ n₁ h).symm (w n₁) (w' n₁)

variable {F φ n₀ n₁ h} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
include h hT hT'

/-- **Four lemma for homology sequences.** For a morphism `φ : T ⟶ T'` of distinguished
triangles, `F^{n₀}(φ.hom₃)` is an epimorphism as soon as `F^{n₀}(φ.hom₂)` and `F^{n₁}(φ.hom₁)`
are epimorphisms and `F^{n₁}(φ.hom₂)` is a monomorphism. -/
lemma epi_shift_map_hom₃ (h₂ : Epi ((F.shift n₀).map φ.hom₂))
    (h₄ : Epi ((F.shift n₁).map φ.hom₁)) (h₅ : Mono ((F.shift n₁).map φ.hom₂)) :
    Epi ((F.shift n₀).map φ.hom₃) :=
  Abelian.epi_of_epi_of_epi_of_mono'' (k := 1) (by lia)
    (F.homologySequenceComposableArrows₅_exact T hT n₀ n₁ h)
    (F.homologySequenceComposableArrows₅_exact T' hT' n₀ n₁ h)
    (F.homologySequenceComposableArrows₅Map φ n₀ n₁ h) 1 2 3 4 rfl rfl rfl rfl h₂ h₄ h₅

/-- **Five lemma for homology sequences.** For a morphism `φ : T ⟶ T'` of distinguished
triangles, `F^{n₀}(φ.hom₃)` is an isomorphism as soon as `F^{n₀}(φ.hom₁)` is an epimorphism,
`F^{n₀}(φ.hom₂)` and `F^{n₁}(φ.hom₁)` are isomorphisms and `F^{n₁}(φ.hom₂)` is a
monomorphism. -/
lemma isIso_shift_map_hom₃ (h₁ : Epi ((F.shift n₀).map φ.hom₁))
    (h₂ : IsIso ((F.shift n₀).map φ.hom₂)) (h₄ : IsIso ((F.shift n₁).map φ.hom₁))
    (h₅ : Mono ((F.shift n₁).map φ.hom₂)) :
    IsIso ((F.shift n₀).map φ.hom₃) :=
  Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 0) (by lia)
    (F.homologySequenceComposableArrows₅_exact T hT n₀ n₁ h)
    (F.homologySequenceComposableArrows₅_exact T' hT' n₀ n₁ h)
    (F.homologySequenceComposableArrows₅Map φ n₀ n₁ h) 0 1 2 3 4 rfl rfl rfl rfl rfl h₁ h₂ h₄ h₅

end CategoryTheory.Functor
