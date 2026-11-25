/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechSheafResolution
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Hom comparison for the sheafified presheaf Čech nerve

Source: Stacks Project, Cohomology on Sites, Tag 079Z, zero-row identification.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The free-sheaf adjunction identifies Hom cochains with presheaf Čech cochains,
including their differentials. No covering or Ext vanishing is assumed.
Source: Stacks Project, Cohomology on Sites, Tag 079Z, zero-row identification.
(blueprint: lem-sc-presheaf-cech-sheaf-hom-comparison)

Proof: in every degree apply the sheafification adjunction to identify morphisms
from the sheafified free nerve term to F with presheaf morphisms from the free
nerve term to F.obj. These Hom equivalences are additive: their forward and
inverse maps are composition with the unit and counit and application of the
additive sheafification and forgetful functors. The nerve terms, after applying
free abelian presheaves, are exactly the terms defining presheafCechComplex.
Naturality of the adjunction identifies precomposition with every face map.
Additivity then identifies precomposition with the alternating sum of faces
with the alternating coface differential. This gives the displayed identity
for every n and every cochain a, including degree zero and empty fibres.
-/
theorem presheafCechSheafComplex_hom_comparison
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    (F : Sheaf J AddCommGrpCat.{v}) (f : Arrow (Cᵒᵖ ⥤ Type v)) :
    ∃ e : ∀ n, ((presheafCechSheafComplex J f).X n ⟶ F) ≃+
        (presheafCechComplex f F.obj).X n,
      ∀ n (a : (presheafCechSheafComplex J f).X n ⟶ F),
        e (n + 1) ((presheafCechSheafComplex J f).d (n + 1) n ≫ a) =
          (presheafCechComplex f F.obj).d n (n + 1) (e n a) := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{v}
  let E := fun P : Cᵒᵖ ⥤ AddCommGrpCat.{v} ↦ adj.homAddEquiv P F
  refine ⟨fun n ↦ E ((f.cechNerve.obj (Opposite.op (SimplexCategory.mk n))) ⋙
    AddCommGrpCat.free), ?_⟩
  intro n a
  simp only [presheafCechSheafComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change E _ (AlgebraicTopology.AlternatingFaceMapComplex.objD
    (f.cechNerve ⋙ presheafCechFreeSheafFunctor J) n ≫ a) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, map_sum, map_zsmul]
  simp only [presheafCechComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  simp only [← AddCommGrpCat.homAddEquiv_apply, map_sum, map_zsmul,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact adj.homEquiv_naturality_left (Functor.whiskerRight (f.cechNerve.δ j)
    AddCommGrpCat.free) a

end CategoryTheory.Sheaf
