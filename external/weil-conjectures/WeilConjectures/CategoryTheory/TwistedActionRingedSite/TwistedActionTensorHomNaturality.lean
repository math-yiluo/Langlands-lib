/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement

/-! # Naturality of the transpose of a tensor comparison

Source: Stacks, sites-modules.tex, lemma-internal-hom-adjoint-tensor.
(blueprint: lem-sf-tensor-hom-comparison-precomposition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

private theorem untranspose_evaluation
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N Q : Modules S)
    (f : Q ⟶ SheafOfModules.homObj (R := S) M N) :
    (SheafOfModules.tensorHomEquiv (R := S) M Q N).symm f =
      tensorMap (𝟙 M) f ≫ evaluationMap M N := by
  apply (SheafOfModules.tensorHomEquiv (R := S) M Q N).injective
  simp only [Equiv.apply_symm_apply, tensorMap, id_tensorHom,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp, evaluationMap, Category.comp_id]

/-- A functor with a tensor comparison sends untransposes to the corresponding
untransposes composed with its canonical Hom comparison.
Source: Stacks, sites-modules.tex, lemma-internal-hom-adjoint-tensor.
(blueprint: lem-sf-tensor-hom-comparison-precomposition).

Proof: express an untranspose as tensoring the given map with the identity and
then evaluating. Move the tensor comparison past that map by its naturality.
The inverse tensor comparison followed by mapped evaluation is the untranspose
of the canonical Hom comparison, by the inverse laws of the tensor-Hom
adjunction. Tensor functoriality combines the two Hom maps, giving the formula.
No faithfulness, essential surjectivity, or action structure is used. -/
theorem tensorHomComparison_precomp
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (U : Modules S ⥤ Modules R)
    (t : ∀ M N : Modules S, U.obj (tensorObj M N) ≅ tensorObj (U.obj M) (U.obj N))
    (ht : ∀ (M Q H : Modules S) (f : Q ⟶ H),
      U.map (tensorMap (𝟙 M) f) ≫ (t M H).hom =
        (t M Q).hom ≫ tensorMap (𝟙 (U.obj M)) (U.map f))
    (M N Q : Modules S) (f : Q ⟶ SheafOfModules.homObj (R := S) M N) :
    U.map ((SheafOfModules.tensorHomEquiv (R := S) M Q N).symm f) =
      (t M Q).hom ≫ tensorMap (𝟙 (U.obj M))
        (U.map f ≫ SheafOfModules.tensorHomEquiv (R := R) _ _ _
          ((t M (SheafOfModules.homObj (R := S) M N)).inv ≫
            U.map (evaluationMap M N))) ≫ evaluationMap (U.obj M) (U.obj N) := by
  let H := SheafOfModules.homObj (R := S) M N
  let b := SheafOfModules.tensorHomEquiv (R := R) _ _ _
    ((t M H).inv ≫ U.map (evaluationMap M N))
  have he : tensorMap (𝟙 (U.obj M)) b ≫ evaluationMap (U.obj M) (U.obj N) =
      (t M H).inv ≫ U.map (evaluationMap M N) := by
    rw [← untranspose_evaluation]
    exact (SheafOfModules.tensorHomEquiv (R := R) _ _ _).symm_apply_apply _
  change U.map ((SheafOfModules.tensorHomEquiv (R := S) M Q N).symm f) =
    (t M Q).hom ≫ tensorMap (𝟙 (U.obj M)) (U.map f ≫ b) ≫
      evaluationMap (U.obj M) (U.obj N)
  rw [untranspose_evaluation, U.map_comp]
  calc
    _ = (t M Q).hom ≫ tensorMap (𝟙 (U.obj M)) (U.map f) ≫
        (t M H).inv ≫ U.map (evaluationMap M N) := by
      rw [← Category.assoc, ← Category.assoc, ← ht M Q H f]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [← he]
      simp only [tensorMap, id_tensorHom, Category.assoc, whiskerLeft_comp]

end CategoryTheory.TwistedActionRingedSite
