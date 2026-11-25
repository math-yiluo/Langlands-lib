/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Composing a derived functor with a functor

Let `Φ : LocalizerMorphism W₁ W₂` be a left derivability structure, `L₂ : C₂ ⥤ D₂` a
localization functor for `W₂`, and `α : L₂ ⋙ LF ⟶ F` a natural transformation which is an
isomorphism at every object `Φ.functor.obj X₁`. Then for any functor `G : H ⥤ H'`, the
composite `LF ⋙ G` is a left derived functor of `F ⋙ G`, with the whiskered 2-cell
```
      L₂
  C₂ ────▶ D₂
    ╲  ⇓α  │
   F ╲     │ LF
      ▼    ▼
       H ──G──▶ H'
```
(`LocalizerMorphism.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure`). The dual
statement for right derivability structures is
`LocalizerMorphism.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure`.

These are the "absoluteness" hypotheses of `CategoryTheory.Adjunction.derived` when the
derived functors are computed with derivability structures.
-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ D₂ H H' : Type*} [Category* C₁] [Category* C₂] [Category* D₂]
  [Category* H] [Category* H']
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂) {F : C₂ ⥤ H} {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂]

namespace LocalizerMorphism

/-- If `α : L₂ ⋙ LF ⟶ F` is an isomorphism on the objects coming from a left derivability
structure `Φ`, then for any `G`, `LF ⋙ G` is a left derived functor of `F ⋙ G` for the
2-cell `L₂ ⋙ LF ⋙ G ⟶ F ⋙ G` induced by `α`. -/
lemma isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure
    [Φ.IsLeftDerivabilityStructure] {LF : D₂ ⥤ H} (α : L₂ ⋙ LF ⟶ F)
    (hα : ∀ X₁ : C₁, IsIso (α.app (Φ.functor.obj X₁))) (G : H ⥤ H') :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α G) W₂ :=
  Φ.isLeftDerivedFunctor_of_isLeftDerivabilityStructure _ fun X₁ ↦ by
    have := hα X₁
    dsimp
    infer_instance

/-- If `α : F ⟶ L₂ ⋙ RF` is an isomorphism on the objects coming from a right derivability
structure `Φ`, then for any `G`, `RF ⋙ G` is a right derived functor of `F ⋙ G` for the
2-cell `F ⋙ G ⟶ L₂ ⋙ RF ⋙ G` induced by `α`. -/
lemma isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
    [Φ.IsRightDerivabilityStructure] {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF)
    (hα : ∀ X₁ : C₁, IsIso (α.app (Φ.functor.obj X₁))) (G : H ⥤ H') :
    (RF ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight α G ≫ (Functor.associator _ _ _).hom) W₂ :=
  Φ.isRightDerivedFunctor_of_isRightDerivabilityStructure _ fun X₁ ↦ by
    have := hα X₁
    dsimp
    infer_instance

end LocalizerMorphism

end CategoryTheory
