/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The inclusion of a Day reflective subcategory preserves internal homs

Let `R : C ⥤ D` be a reflective subcategory of a symmetric monoidal closed category with monoidal
reflector `L`, and give `C` the closed structure of Day's reflection theorem
(`CategoryTheory.Monoidal.Reflective.monoidalClosed`). The comparison map
`R [c, d] ⟶ [R c, R d]` of the lax monoidal functor `R` is the inverse of the unit of `L ⊣ R` at
`[R c, R d]` (`CategoryTheory.Monoidal.Reflective.ihomComparison_app`), hence an isomorphism.
This applies to sheaves inside presheaves.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal
  Functor.Monoidal

namespace CategoryTheory.Monoidal.Reflective

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D] [MonoidalCategory C]
  {L : D ⥤ C} [L.Monoidal] {R : C ⥤ D} [R.Faithful] [R.Full] (adj : L ⊣ R)

/-- For the closed structure given by Day's reflection theorem, the comparison map
`R [c, d] ⟶ [R c, R d]` of the inclusion `R` (lax monoidal as right adjoint of the monoidal
reflector) is the inverse of the unit `[R c, R d] ⟶ R L [R c, R d]`. -/
lemma ihomComparison_app :
    letI := monoidalClosed adj
    letI := adj.rightAdjointLaxMonoidal
    ∀ (c d : C), (ihomComparison R c).app d =
      inv (adj.unit.app ((ihom (R.obj c)).obj (R.obj d))) := by
  let := monoidalClosed adj
  let := adj.rightAdjointLaxMonoidal
  intro c d
  rw [ihomComparison_app_eq_curry, curry_eq_iff, uncurry_eq]
  let comm1 : R ⋙ tensorLeft (R.obj c) ⋙ L ≅ tensorLeft c ⋙ 𝟭 C :=
    NatIso.ofComponents (fun _ ↦ (μIso L _ _).symm ≪≫
        asIso ((adj.counit.app _) ⊗ₘ (adj.counit.app _))) (fun _ ↦ by
      dsimp
      rw [Category.assoc, ← δ_natural_right_assoc,
        tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc,
        Adjunction.counit_naturality, whisker_exchange,
        tensorHom_def_assoc, MonoidalCategory.whiskerLeft_comp])
  let comm2 : 𝟭 C ⋙ R ⋙ ihom (R.obj c) ≅ (R ⋙ ihom (R.obj c) ⋙ L) ⋙ R :=
    NatIso.ofComponents (fun _ ↦ asIso (adj.unit.app ((ihom _).obj _)))
  have hev : (ihom.ev c).app d = (𝟭 C).map ((((ihom.adjunction (R.obj c)).comp
      adj).restrictFullyFaithful (Functor.FullyFaithful.ofFullyFaithful R)
      (Functor.FullyFaithful.id _) comm1 comm2).counit.app d) := rfl
  rw [hev, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [comm1, comm2, NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv, asIso_inv,
    μIso_hom, Functor.comp_map,  Adjunction.comp_counit_app, Functor.id_obj,
    Functor.comp_obj, Adjunction.rightAdjointLaxMonoidal_μ]
  rw [Adjunction.homEquiv_unit, Category.assoc, ← R.map_comp]
  have key : adj.unit.app (R.obj c ⊗ R.obj (L.obj ((ihom (R.obj c)).obj (R.obj d)))) ≫
      R.map ((δ L (R.obj c) (R.obj (L.obj ((ihom (R.obj c)).obj (R.obj d)))) ≫
        (adj.counit.app c ⊗ₘ adj.counit.app (L.obj ((ihom (R.obj c)).obj (R.obj d))))) ≫
        (inv (adj.counit.app c ⊗ₘ adj.counit.app (L.obj ((ihom (R.obj c)).obj (R.obj d)))) ≫
          μ L (R.obj c) (R.obj (L.obj ((ihom (R.obj c)).obj (R.obj d))))) ≫
        L.map (R.obj c ◁ inv (adj.unit.app ((ihom (R.obj c)).obj (R.obj d)))) ≫
        L.map ((ihom.ev (R.obj c)).app (R.obj d)) ≫ adj.counit.app d) =
      R.obj c ◁ inv (adj.unit.app ((ihom (R.obj c)).obj (R.obj d))) ≫
        (ihom.ev (R.obj c)).app (R.obj d) := by
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, δ_μ_assoc]
    rw [← L.map_comp_assoc, R.map_comp]
    erw [adj.unit_naturality_assoc]
    erw [Adjunction.right_triangle_components, Category.comp_id]
  exact key

/-- For the closed structure given by Day's reflection theorem, the inclusion of the reflective
subcategory commutes with internal homs. -/
lemma isIso_ihomComparison :
    letI := monoidalClosed adj
    letI := adj.rightAdjointLaxMonoidal
    ∀ c : C, IsIso (ihomComparison R c) := by
  let := monoidalClosed adj
  let := adj.rightAdjointLaxMonoidal
  intro c
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  rw [ihomComparison_app]
  infer_instance

end CategoryTheory.Monoidal.Reflective
