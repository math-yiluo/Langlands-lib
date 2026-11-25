/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsCore

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace MonoidalCategory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_hom_ext {Y : Scheme.{u}} {M N H : Y.Modules}
    {a b : M ⊗ N ⟶ H}
    (h : ∀ (W : Y.Opens) (s : Γ(M, W)) (t : Γ(N, W)),
      a.app W (tmulSection s t) = b.app W (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) H).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h W.unop s t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_right_triple_hom_ext {Y : Scheme.{u}} {M N L H : Y.Modules}
    {a b : M ⊗ (N ⊗ L) ⟶ H}
    (h : ∀ (W : Y.Opens) (s : Γ(M, W)) (t : Γ(N, W)) (w : Γ(L, W)),
      a.app W (tmulSection s (tmulSection t w)) =
        b.app W (tmulSection s (tmulSection t w))) : a = b := by
  let := presheafMonoidalCategory Y
  let := forgetToPresheafOfModulesLaxMonoidal Y
  apply tensor_hom_ext
  intro U s w
  let μ := Functor.LaxMonoidal.μ (forgetToPresheafOfModules Y) N L
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology Y)
    ((PresheafOfModules.toPresheaf _).map μ) (U := op U) w
  refine (H.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W i hi ↦ ?_
  obtain ⟨z, hz⟩ := hi
  have hz' : tensorSectionsMap N L W z = (N ⊗ L).presheaf.map i.op w := hz
  have hh (z : TensorProduct Γ(Y, W) Γ(N, W) Γ(L, W)) :
      a.app W (tmulSection (M.presheaf.map i.op s) (tensorSectionsMap N L W z)) =
        b.app W (tmulSection (M.presheaf.map i.op s) (tensorSectionsMap N L W z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul t w => exact h W (M.presheaf.map i.op s) t w
    | add z z' hz hz' => simp only [map_add, tmulSection_add, hz, hz']
  change H.presheaf.map i.op (a.app U (tmulSection s w)) =
    H.presheaf.map i.op (b.app U (tmulSection s w))
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  have ht := tmulSection_map (leOfHom i) s w
  rw [Subsingleton.elim (homOfLE (leOfHom i)) i] at ht
  rw [ht]
  exact hz' ▸ hh z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The balancing identity for maps satisfying the section formulas.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-balancing).

Proof: morphisms from a tensor sheaf are determined on pure tensor sections,
by the sheafification adjunction and the sectionwise tensor universal property.
For the iterated tensor, the inner tensorator is locally surjective. Locally
lift its section to a sum of pure tensors and use additivity and separatedness
of the target. Thus it suffices to test b tensor (c tensor p). The three
formulas reduce the desired equality to the image under the sheafification
unit of c tensor_B bp = φ(b)c tensor_B p. This is the balanced tensor identity.
-/
theorem changeOfRings_tensor_action_comp_eq (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
    (g : tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) ⟶
      (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P))
    (h : ChangeOfRingsTensorActionFormulas Y B C φ P a d g) :
    a ≫ g = d ≫ g := by
  apply tensor_right_triple_hom_ext
  intro W b c p
  change B.right.obj.obj (op W) at b
  change C.right.obj.obj (op W) at c
  change P.val.obj (op W) at p
  change g.app W (a.app W (tmulSection b (tmulSection c p))) =
    g.app W (d.app W (tmulSection b (tmulSection c p)))
  rw [h.1 W b c p, h.2.1 W b c p, h.2.2 W c (b • p),
    h.2.2 W (φ.right.hom.app (op W) b * c) p]
  congr 1
  let : Module (B.right.obj.obj (op W)) (C.right.obj.obj (op W)) :=
    Module.compHom _ (φ.right.hom.app (op W)).hom
  rw [TensorProduct.tmul_smul]
  rfl


end AlgebraicGeometry.Scheme.Modules
