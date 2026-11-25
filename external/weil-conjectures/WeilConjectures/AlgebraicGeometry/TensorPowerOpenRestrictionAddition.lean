/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN

/-! # Addition of tensor powers under open restriction

Source: Stacks Project, Modules, Tag 01CD, iterated tensor-pullback comparison.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
open Opposite TopologicalSpace in
private theorem tensor_hom_ext {Y : Scheme.{u}} {M N H : Y.Modules}
    {a b : M ⊗ N ⟶ H}
    (h : ∀ (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  let := presheafMonoidalCategory Y
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) H).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul s t => exact h U.unop s t
  | add z w hz hw => simp only [map_add, hz, hw]

set_option backward.isDefEq.respectTransparency false in
open Opposite TopologicalSpace in
private theorem tensor_triple_hom_ext {Y : Scheme.{u}} {M N L H : Y.Modules}
    {a b : (M ⊗ N) ⊗ L ⟶ H}
    (h : ∀ (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) (w : Γ(L, U)),
      a.app U (tmulSection (tmulSection s t) w) =
        b.app U (tmulSection (tmulSection s t) w)) : a = b := by
  let := presheafMonoidalCategory Y
  let := forgetToPresheafOfModulesLaxMonoidal Y
  apply tensor_hom_ext
  intro U s w
  let μ := Functor.LaxMonoidal.μ (forgetToPresheafOfModules Y) M N
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology Y)
    ((PresheafOfModules.toPresheaf _).map μ) (U := op U) s
  refine (H.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W i hi ↦ ?_
  obtain ⟨z, hz⟩ := hi
  have hz' : tensorSectionsMap M N W z = (M ⊗ N).presheaf.map i.op s := hz
  have hh (z : TensorProduct Γ(Y, W) Γ(M, W) Γ(N, W)) :
      a.app W (tmulSection (tensorSectionsMap M N W z) (L.presheaf.map i.op w)) =
        b.app W (tmulSection (tensorSectionsMap M N W z) (L.presheaf.map i.op w)) := by
    induction z using TensorProduct.inductionOn with
    | tmul s t => exact h W s t (L.presheaf.map i.op w)
    | add z z' hz hz' => simp only [map_add, add_tmulSection, hz, hz']
  change H.presheaf.map i.op (a.app U (tmulSection s w)) =
    H.presheaf.map i.op (b.app U (tmulSection s w))
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  have ht := tmulSection_map (leOfHom i) s w
  rw [Subsingleton.elim (homOfLE (leOfHom i)) i] at ht
  rw [ht]
  exact hz' ▸ hh z

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_inv_tmul {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) (V : Y.Opens)
    (z : Γ(F.restrict j, V)) (w : Γ(G.restrict j, V)) :
    ((openRestrictionTensorIso j F G).inv.app V (tmulSection z w)) =
      tmulSection (M := F) (N := G) (U := j ''ᵁ V) z w := by
  exact Classical.choose_spec (exists_restriction_tensor_comparison j F G) V z w

set_option backward.isDefEq.respectTransparency false in
private theorem power_inv_tmul {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (n : ℕ) (V : Y.Opens)
    (z : Γ(L.restrict j, V)) (w : Γ((L.restrict j).tensorPow n, V)) :
    (openRestrictionTensorPowIso j L (n + 1)).inv.app V (tmulSection z w) =
      tmulSection (M := L) (N := L.tensorPow n) (U := j ''ᵁ V) z
        ((openRestrictionTensorPowIso j L n).inv.app V w) := by
  change (openRestrictionTensorIso j L (L.tensorPow n)).inv.app V
    (((𝟙 (L.restrict j)) ⊗ₘ (openRestrictionTensorPowIso j L n).inv).app V
      (tmulSection z w)) = _
  rw [tensorHom_app_tmulSection, Hom.id_app, ConcreteCategory.id_apply,
    comparison_inv_tmul]

set_option backward.isDefEq.respectTransparency false in
private theorem transport_comparison {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) {n m : ℕ} (h : n = m) :
    eqToHom (congrArg (L.restrict j).tensorPow h) ≫
        (openRestrictionTensorPowIso j L m).inv =
      (openRestrictionTensorPowIso j L n).inv ≫
        (restrictFunctor j).map (eqToHom (congrArg L.tensorPow h)) := by
  subst m
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem addition_comparison {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (n b : ℕ) :
    ((L.restrict j).tensorPowAddIso n b).inv ≫
        (openRestrictionTensorPowIso j L (n + b)).inv =
      ((openRestrictionTensorPowIso j L n).inv ⊗ₘ
        (openRestrictionTensorPowIso j L b).inv) ≫
        (openRestrictionTensorIso j (L.tensorPow n) (L.tensorPow b)).inv ≫
        (restrictFunctor j).map (L.tensorPowAddIso n b).inv := by
  induction n with
  | zero =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Functor.map_comp, Category.assoc]
    rw [transport_comparison j L (Nat.zero_add b).symm]
    simp only [← Category.assoc]
    apply (cancel_mono _).mpr
    apply tensor_hom_ext
    intro V z w
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection,
      comparison_inv_tmul]
    change (openRestrictionTensorPowIso j L b).inv.app V
      ((λ_ ((L.restrict j).tensorPow b)).hom.app V (tmulSection z w)) =
      (λ_ (L.tensorPow b)).hom.app (j ''ᵁ V)
        (tmulSection ((openRestrictionTensorPowIso j L 0).inv.app V z)
          ((openRestrictionTensorPowIso j L b).inv.app V w))
    rw [leftUnitor_hom_app_tmulSection', leftUnitor_hom_app_tmulSection']
    rw [Hom.app_smul]
    rfl
  | succ n ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Functor.map_comp, Category.assoc]
    rw [transport_comparison j L (Nat.succ_add n b).symm]
    simp only [← Category.assoc]
    apply (cancel_mono _).mpr
    apply tensor_triple_hom_ext
    intro V z t w
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    change (openRestrictionTensorPowIso j L (n + b + 1)).inv.app V
      (((𝟙 (L.restrict j)) ⊗ₘ ((L.restrict j).tensorPowAddIso n b).inv).app V
        ((α_ (L.restrict j) ((L.restrict j).tensorPow n)
          ((L.restrict j).tensorPow b)).hom.app V (tmulSection (tmulSection z t) w))) =
      ((𝟙 L) ⊗ₘ (L.tensorPowAddIso n b).inv).app (j ''ᵁ V)
        ((α_ L (L.tensorPow n) (L.tensorPow b)).hom.app (j ''ᵁ V)
          ((openRestrictionTensorIso j (L.tensorPow (n + 1)) (L.tensorPow b)).inv.app V
            (((openRestrictionTensorPowIso j L (n + 1)).inv ⊗ₘ
              (openRestrictionTensorPowIso j L b).inv).app V
                (tmulSection (tmulSection z t) w))))
    rw [associator_hom_app_tmulSection, tensorHom_app_tmulSection,
      Hom.id_app, ConcreteCategory.id_apply, power_inv_tmul,
      tensorHom_app_tmulSection, power_inv_tmul, comparison_inv_tmul,
      associator_hom_app_tmulSection, tensorHom_app_tmulSection,
      Hom.id_app, ConcreteCategory.id_apply]
    have hi := congrArg (fun f ↦ f.app V (tmulSection t w)) ih
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection,
      comparison_inv_tmul] at hi
    exact congrArg (tmulSection (M := L) (U := j ''ᵁ V) z) hi

set_option backward.isDefEq.respectTransparency false in
/-- The recursive power comparison intertwines addition of exponents on pure tensors
of arbitrary sections of the two powers. No section of L is fixed.
Source: Stacks Project, Modules, Tag 01CD, tensor-pullback comparison.
(blueprint: lem-sc-tensor-power-open-restriction-addition).

Proof: First use the pure-tensor characterization of openRestrictionTensorIso and
uniqueness in the sheaf tensor universal property to establish naturality and
associator coherence. For unitor coherence, the unit comparison is the structure-ring
isomorphism, and the unitor multiplies a section by its scalar; restriction transports
this scalar through the same ring isomorphism. Induct on n in tensorPowAddIso.
For n = 0 its inverse is the left unitor followed by the exponent equality transport;
the just established unitor coherence gives the result for every scalar and section.
For n + 1 expand its inverse into the associator, tensor of the identity with the
previous addition inverse, and exponent equality transport. Associator coherence and
the inductive hypothesis identify the two composites as sheaf morphisms. Evaluate
that equality on tmulSection z w over V to obtain the displayed formula. The sheaf
universal property, rather than generation of global sections by pure tensors,
extends the checks to all sections of the powers. Equality transport commutes with
restriction by elimination of the exponent equality. This also covers zero modules,
the empty open, and either exponent zero. -/
theorem openRestrictionTensorPowIso_inv_add {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (n b : ℕ) (V : Y.Opens)
    (z : Γ((L.restrict j).tensorPow n, V))
    (w : Γ((L.restrict j).tensorPow b, V)) :
    ((L.tensorPow (n + b)).restrictAppIso j V).hom
        ((openRestrictionTensorPowIso j L (n + b)).inv.app V
          (((L.restrict j).tensorPowAddIso n b).inv.app V (tmulSection z w))) =
      (L.tensorPowAddIso n b).inv.app (j ''ᵁ V)
        (tmulSection
          (((L.tensorPow n).restrictAppIso j V).hom
            ((openRestrictionTensorPowIso j L n).inv.app V z))
          (((L.tensorPow b).restrictAppIso j V).hom
            ((openRestrictionTensorPowIso j L b).inv.app V w))) := by
  have h := congrArg (fun f ↦ f.app V (tmulSection z w))
    (addition_comparison j L n b)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection,
    comparison_inv_tmul] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
