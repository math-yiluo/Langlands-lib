/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.CategoryTheory.Endofunctor.StrictPairTensor
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Tensor powers of scalar twists of the unit pair

For a monoidal endofunctor `P` of a monoidal category, the unit `𝟙` with the structure
`P 𝟙 ≅ 𝟙` inverse to the unit constraint of `P`, multiplied by an automorphism `s` of `𝟙`, is a
strict pair `(𝟙, η ≫ s)` (`CategoryTheory.Endofunctor.IsoAlgebra.unitScalarPair`). Tensoring
`(𝟙, η ≫ s)` with `(𝟙, η ≫ t)` (`CategoryTheory.Endofunctor.IsoAlgebra.tensorWith`) gives
`(𝟙, η ≫ s ≫ t)` under the unit constraint `𝟙 ⊗ 𝟙 ≅ 𝟙`
(`CategoryTheory.Endofunctor.IsoAlgebra.unitScalarPairTensorIso`): the scalars multiply. This
is the formal content of the tensor powers of the Tate twist `ℚ̄_ℓ(d) = ℚ̄_ℓ(1)^{⊗ d}` in the
condensed model of Weil sheaves, where the Weil structure of `ℚ̄_ℓ(1)` is the cyclotomic unit
`χ_ℓ(σ)` times that of `ℚ̄_ℓ`.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : C ⥤ C) [P.Monoidal]

/-- The strict pair `(𝟙, η ≫ s)`: the unit with the inverse unit constraint of `P` as structure,
multiplied by an automorphism `s` of the unit. -/
def unitScalarPair (s : 𝟙_ C ≅ 𝟙_ C) : IsoAlgebra P :=
  mk (𝟙_ C) ((Functor.Monoidal.εIso P).symm ≪≫ s)

@[simp]
lemma unitScalarPair_carrier (s : 𝟙_ C ≅ 𝟙_ C) : (unitScalarPair P s).carrier = 𝟙_ C :=
  rfl

lemma unitScalarPair_obj_str (s : 𝟙_ C ≅ 𝟙_ C) :
    (unitScalarPair P s).obj.str = η P ≫ s.hom :=
  rfl

/-- The structure of the tensor product of `(𝟙, η ≫ s)` with `(𝟙, η ≫ t)`, unfolded. -/
lemma tensorWith_obj_unitScalarPair_obj_str (s t : 𝟙_ C ≅ 𝟙_ C) :
    ((tensorWith P ((Functor.Monoidal.εIso P).symm ≪≫ t)).obj (unitScalarPair P s)).obj.str =
      δ P (𝟙_ C) (𝟙_ C) ≫ ((η P ≫ s.hom) ⊗ₘ (η P ≫ t.hom)) :=
  rfl

/-- The unit constraint of `P` against the left unitor: `P (λ_ 𝟙) = δ ≫ η ▷ P 𝟙 ≫ λ_ (P 𝟙)`. -/
lemma δ_comp_whiskerRight_η_comp_leftUnitor_hom :
    δ P (𝟙_ C) (𝟙_ C) ≫ η P ▷ P.obj (𝟙_ C) ≫ (λ_ (P.obj (𝟙_ C))).hom =
      P.map (λ_ (𝟙_ C)).hom := by
  rw [Functor.LaxMonoidal.left_unitality, ← MonoidalCategory.comp_whiskerRight_assoc,
    Functor.Monoidal.η_ε, MonoidalCategory.id_whiskerRight, Category.id_comp,
    Functor.Monoidal.δ_μ_assoc]

/-- **Scalars multiply under tensor products**: tensoring the strict pair `(𝟙, η ≫ s)` with
`(𝟙, η ≫ t)` gives `(𝟙, η ≫ s ≫ t)`, under the unit constraint `𝟙 ⊗ 𝟙 ≅ 𝟙`. -/
def unitScalarPairTensorIso (s t : 𝟙_ C ≅ 𝟙_ C) :
    (tensorWith P ((Functor.Monoidal.εIso P).symm ≪≫ t)).obj (unitScalarPair P s) ≅
      unitScalarPair P (s ≪≫ t) :=
  isoMk (λ_ (𝟙_ C)) (by
    have hx : s.hom ▷ P.obj (𝟙_ C) ≫ 𝟙_ C ◁ η P = 𝟙_ C ◁ η P ≫ s.hom ▷ 𝟙_ C :=
      (whisker_exchange _ _).symm
    have hlt : 𝟙_ C ◁ t.hom ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ t.hom :=
      MonoidalCategory.leftUnitor_naturality _
    have hrs : s.hom ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ s.hom := by
      rw [MonoidalCategory.unitors_equal]
      exact MonoidalCategory.rightUnitor_naturality _
    have hle : 𝟙_ C ◁ η P ≫ (λ_ (𝟙_ C)).hom = (λ_ (P.obj (𝟙_ C))).hom ≫ η P :=
      MonoidalCategory.leftUnitor_naturality _
    rw [tensorWith_obj_unitScalarPair_obj_str, unitScalarPair_obj_str,
      ← δ_comp_whiskerRight_η_comp_leftUnitor_hom, tensorHom_def,
      MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc, Iso.trans_hom]
    rw [reassoc_of% hx, hlt, reassoc_of% hrs, reassoc_of% hle])

end CategoryTheory.Endofunctor.IsoAlgebra
