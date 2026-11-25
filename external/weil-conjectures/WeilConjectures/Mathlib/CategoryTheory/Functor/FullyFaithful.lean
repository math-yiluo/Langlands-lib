/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.Yoneda

/-!
# Fully faithful functors and the Yoneda embedding

For a fully faithful functor `F : C ⥤ D` and `A : C`, the functor `T ↦ Hom(F T, F A)` is
isomorphic to `T ↦ Hom(T, A)`, naturally in `A` and `T`.
-/

@[expose] public section

universe v u₁ u₂

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D] {F : C ⥤ D}

/-- For a fully faithful functor `F`, the isomorphisms `Hom(F T, F A) ≅ Hom(T, A)`, natural in
`A` and `T`. -/
noncomputable def compYonedaCompWhiskeringLeftIso (hF : F.FullyFaithful) :
    F ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ≅ yoneda :=
  NatIso.ofComponents hF.opCompYonedaObjIso
    (fun g ↦ by ext T x; exact hF.map_injective (by simp [opCompYonedaObjIso]))

end CategoryTheory.Functor.FullyFaithful
