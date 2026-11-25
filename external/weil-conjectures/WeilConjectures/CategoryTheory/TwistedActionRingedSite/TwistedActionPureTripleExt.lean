/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement

/-! # Extensionality on iterated sheafified pure tensors -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}}

attribute [local irreducible] SheafOfModules.monoidalCategory

private abbrev tensorAdj := PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)

/-- Maps from an iterated sheaf tensor agree if they agree on all pure triples.

Source: Stacks 03EK, sheaf tensor as the sheafification of presheaf tensor
(blueprint: lem-sf-sheaf-tensor-pure-triple-ext).

Proof: tensor the inner sheafification unit with the third factor, then sheafify.
This morphism is invertible because tensor preserves local equivalences. Compose
it with the two tensor/sheafification comparison isomorphisms and cancel the result.
The sheafification adjunction reduces the remaining equality to presheaf maps, where
sectionwise triple tensor extensionality applies. Naturality of the adjunction unit
and the pure-tensor map formula identify each tested generator with the prescribed
sheafified pure triple. Thus no assertion of global pure generation is needed. -/
theorem pure_triple_ext (M N T H : Modules S) {f g : (M ⊗ N) ⊗ T ⟶ H}
    (h : ∀ X x y z,
      f.val.app X (pureTensor (M ⊗ N) T X (pureTensor M N X x y) z) =
      g.val.app X (pureTensor (M ⊗ N) T X (pureTensor M N X x y) z)) : f = g := by
  let adj := tensorAdj (S := S)
  let F := PresheafOfModules.sheafification (𝟙 (ring S).obj)
  let E := M.val ⊗ N.val
  have hη : (K.W.inverseImage (PresheafOfModules.toPresheaf (ring S).obj))
      (adj.unit.app E) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ring S).obj)]
    change IsIso (F.map (adj.unit.app E))
    infer_instance
  have hi : IsIso (F.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val)) := by
    have ht := (K.W.inverseImage (PresheafOfModules.toPresheaf (ring S).obj)).tensorHom_mem
      (adj.unit.app E) (𝟙 T.val) hη
      ((K.W.inverseImage (PresheafOfModules.toPresheaf (ring S).obj)).id_mem _)
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ring S).obj)] at ht
    exact ht
  let q := F.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (F.obj E) T).inv ≫
      ((SheafOfModules.tensorObjIsoSheafification M N).inv ⊗ₘ 𝟙 T)
  have : IsIso q := by dsimp only [q]; infer_instance
  have he (X : Dᵒᵖ) (x : M.val.obj X) (y : N.val.obj X) (z : T.val.obj X) :
      q.val.app X ((adj.unit.app (E ⊗ T.val)).app X
        ((x ⊗ₜ[S.obj.obj X] y) ⊗ₜ[S.obj.obj X] z)) =
      pureTensor (M ⊗ N) T X (pureTensor M N X x y) z := by
    have hn := congrArg (fun k ↦ k.app X
      ((x ⊗ₜ[S.obj.obj X] y) ⊗ₜ[S.obj.obj X] z))
        (adj.unit.naturality ((adj.unit.app E) ⊗ₘ 𝟙 T.val))
    change (adj.unit.app ((F.obj E).val ⊗ T.val)).app X
        ((adj.unit.app E).app X (x ⊗ₜ[S.obj.obj X] y) ⊗ₜ[S.obj.obj X] z) =
      (F.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val)).val.app X
        ((adj.unit.app (E ⊗ T.val)).app X
          ((x ⊗ₜ[S.obj.obj X] y) ⊗ₜ[S.obj.obj X] z)) at hn
    change (((SheafOfModules.tensorObjIsoSheafification M N).inv ⊗ₘ 𝟙 T).val.app X)
      ((SheafOfModules.tensorObjIsoSheafification (F.obj E) T).inv.val.app X
        ((F.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val)).val.app X
          ((adj.unit.app (E ⊗ T.val)).app X
            ((x ⊗ₜ[S.obj.obj X] y) ⊗ₜ[S.obj.obj X] z)))) = _
    rw [← hn]
    change (((SheafOfModules.tensorObjIsoSheafification M N).inv ⊗ₘ 𝟙 T).val.app X)
      (pureTensor (F.obj E) T X ((adj.unit.app E).app X (x ⊗ₜ[S.obj.obj X] y)) z) = _
    erw [TensorRestriction.pure_map]
    rfl
  apply (cancel_epi q).mp
  apply (adj.homEquiv (E ⊗ T.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  change f.val.app X (q.val.app X _) = g.val.app X (q.val.app X _)
  exact (congrArg (f.val.app X) (he X x y z)).trans
    ((h X x y z).trans (congrArg (g.val.app X) (he X x y z)).symm)

end CategoryTheory.TwistedActionRingedSite
