/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafFreeNerveExact
public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Free module nerve and abelian Čech cochains

Source: Stacks Project, Cohomology on Sites, Tags 03AS and 03FC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
variable (P : Cᵒᵖ ⥤ Type v) (M : PresheafOfModules.{v} R)
private noncomputable def freeNerveHomEquiv : ((PresheafOfModules.free R).obj P ⟶ M) ≃
    (P ⋙ AddCommGrpCat.free ⟶ M.presheaf) :=
  PresheafOfModules.freeHomEquiv.trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv P M.presheaf).symm
private lemma freeNerveHomEquiv_apply (a : (PresheafOfModules.free R).obj P ⟶ M)
    (X : Cᵒᵖ) (x : P.obj X) :
    ((freeNerveHomEquiv R P M) a).app X (FreeAbelianGroup.of x) =
      a.app X (ModuleCat.freeMk x) := by
  have h := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv P M.presheaf).apply_symm_apply
    (PresheafOfModules.freeHomEquiv a)
  rw [Adjunction.homEquiv_unit] at h
  have hx := congrArg (fun t => (t.app X) x) h
  change ((freeNerveHomEquiv R P M) a).app X (FreeAbelianGroup.of x) =
    a.app X (ModuleCat.freeMk x) at hx
  exact hx

private noncomputable def freeNerveHomAddEquiv : ((PresheafOfModules.free R).obj P ⟶ M) ≃+
    (P ⋙ AddCommGrpCat.free ⟶ M.presheaf) where
  toEquiv := freeNerveHomEquiv R P M
  map_add' a b := by
    apply NatTrans.ext
    funext X
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    change (freeNerveHomEquiv R P M (a + b)).app X (FreeAbelianGroup.of x) =
      (freeNerveHomEquiv R P M a).app X (FreeAbelianGroup.of x) +
        (freeNerveHomEquiv R P M b).app X (FreeAbelianGroup.of x)
    simp only [freeNerveHomEquiv_apply]
    rfl
private lemma freeNerveHomAddEquiv_natural {Q : Cᵒᵖ ⥤ Type v} (t : P ⟶ Q)
    (a : (PresheafOfModules.free R).obj Q ⟶ M) :
    freeNerveHomAddEquiv R P M ((PresheafOfModules.free R).map t ≫ a) =
      Functor.whiskerRight t AddCommGrpCat.free ≫ freeNerveHomAddEquiv R Q M a := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  change (freeNerveHomEquiv R P M ((PresheafOfModules.free R).map t ≫ a)).app X
    (FreeAbelianGroup.of x) =
    (freeNerveHomEquiv R Q M a).app X ((AddCommGrpCat.free.map (t.app X)) (FreeAbelianGroup.of x))
  rw [freeNerveHomEquiv_apply]
  change a.app X ((ModuleCat.free (R.obj X)).map (t.app X) (ModuleCat.freeMk x)) = _
  simp only [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, freeNerveHomEquiv_apply,
    ModuleCat.free_map_apply]


set_option backward.isDefEq.respectTransparency false in
/-- The free module and free abelian adjunctions identify nerve Hom groups
additively, compatibly with the alternating boundaries. No injectivity is used.
Source: Stacks Project, Cohomology on Sites, Tags 03AS and 03FC.
(blueprint: lem-sc-presheaf-free-nerve-comparison)

Proof: in each degree the free module adjunction identifies a module morphism
from the free module presheaf on the nerve with a natural map from that nerve
to the underlying set presheaf of M. The objectwise free abelian adjunction
identifies the same maps with morphisms from the free abelian presheaf into
M.presheaf. Both identifications evaluate a morphism on its basis generators,
so their composite is additive and bijective. They are natural in the nerve
presheaf: precomposing by a free map induced by a face is the same as
precomposing the corresponding abelian map by its free abelian face.
Summing over faces with coefficients (-1)^j proves the displayed boundary
compatibility. This also covers degree zero and empty nerve terms. -/
theorem presheafFreeNerveComplex_comparison
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (M : PresheafOfModules.{v} R) (f : Arrow (Cᵒᵖ ⥤ Type v)) :
    ∃ e : ∀ n : ℕ, ((presheafFreeNerveComplex R f).X n ⟶ M) ≃+
      (presheafCechComplex f M.presheaf).X n,
      ∀ (n : ℕ) (b : (presheafFreeNerveComplex R f).X n ⟶ M),
        e (n + 1) ((presheafFreeNerveComplex R f).d (n + 1) n ≫ b) =
          (presheafCechComplex f M.presheaf).d n (n + 1) (e n b) := by
  refine ⟨fun n => freeNerveHomAddEquiv R (f.cechNerve.obj (Opposite.op (SimplexCategory.mk n))) M,
    ?_⟩
  intro n b
  change (PresheafOfModules.free R).obj
    (f.cechNerve.obj (Opposite.op (SimplexCategory.mk n))) ⟶ M at b
  simp only [presheafFreeNerveComplex,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change freeNerveHomAddEquiv R _ M
    (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (f.cechNerve ⋙ PresheafOfModules.free R) n ≫ b) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, map_sum, map_zsmul]
  simp only [presheafCechComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  simp only [← AddCommGrpCat.homAddEquiv_apply, map_sum,
    map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact freeNerveHomAddEquiv_natural R _ M (f.cechNerve.δ j) b

end CategoryTheory
