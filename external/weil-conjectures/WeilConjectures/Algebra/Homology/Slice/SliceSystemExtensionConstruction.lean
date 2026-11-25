/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic

/-! # Extension of strict coefficient systems to the ambient site

Source: Stacks Project, Modules on Sites, Tags 03DI and 03CY.
(blueprint: lem-sf-slice-system-extension-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r
open CategoryTheory Opposite
attribute [local implicit_reducible] CategoryTheory.sheafCompose

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C)

private theorem extension_unit (A : Sheaf J CommRingCat.{max c v r})
    (G : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
    (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x =
      ringedSliceExtensionSection.{c, v, r} A U G W x := by
  exact (localizedSystemAdjunction_existsUnique.{c, v, r} A U).exists.choose_spec G (op W) x

private theorem extension_ext (A : Sheaf J CommRingCat.{max c v r})
    (G : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
    (K : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J A))
    (f g : (localizedSystemExtension.{c, v, r} A U).obj G ⟶ K)
    (h : ∀ (W : Over U) (x : G.val.obj (op W)), f.val.app (op W.left)
      (ringedSliceExtensionSection.{c, v, r} A U G W x) =
      g.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x)) : f = g := by
  apply ((localizedSystemAdjunction.{c, v, r} A U).homEquiv G K).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change f.val.app (op W.unop.left)
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app W x) =
      g.val.app (op W.unop.left)
        (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app W x)
  rw [extension_unit.{c, v, r} U A G W.unop x]
  exact h W.unop x

private theorem extension_map (A : Sheaf J CommRingCat.{max c v r})
    {G G' : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U)}
    (f : G ⟶ G') (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemExtension.{c, v, r} A U).map f).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) =
      ringedSliceExtensionSection.{c, v, r} A U G' W (f.val.app (op W) x) := by
  have h := congrArg (fun f ↦ f.val.app (op W) x)
    ((localizedSystemAdjunction.{c, v, r} A U).unit.naturality f)
  change ((localizedSystemAdjunction.{c, v, r} A U).unit.app G').val.app (op W)
      (f.val.app (op W) x) =
    ((localizedSystemExtension.{c, v, r} A U).map f).val.app (op W.left)
      (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x) at h
  rw [extension_unit.{c, v, r} U A, extension_unit.{c, v, r} U A] at h
  exact h.symm

private def extensionTransition
    (M : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U))
    {m n : ℕ} (h : m ≤ n) :
    (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj (M.level n) ⟶
      (systemRestriction.{c, v, max c v r} B h).obj
        ((localizedSystemExtension.{c, v, r} (B.obj (op m)) U).obj (M.level m)) := by
  refine ((localizedSystemAdjunction.{c, v, r} (B.obj (op n)) U).homEquiv _ _).symm ?_
  exact M.transition h ≫ (systemRestriction.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B
    U) h).map
    ((localizedSystemAdjunction.{c, v, r} (B.obj (op m)) U).unit.app (M.level m))

private theorem extensionTransition_generator
    (M : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U))
    {m n : ℕ} (h : m ≤ n) (W : Over U) (x : (M.level n).val.obj (op W)) :
    (extensionTransition.{c, v, r} B U M h).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U (M.level n) W x) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op m)) U (M.level m) W
        ((M.transition h).val.app (op W) x) := by
  rw [← extension_unit.{c, v, r} U (B.obj (op n))]
  change (((localizedSystemAdjunction.{c, v, r} (B.obj (op n)) U).homEquiv _ _)
    (extensionTransition.{c, v, r} B U M h)).val.app (op W) x = _
  unfold extensionTransition
  rw [Equiv.apply_symm_apply]
  exact extension_unit.{c, v, r} U (B.obj (op m)) _ W _

private theorem extensionTransition_identity
    (M : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U))
    (n : ℕ) (W : Cᵒᵖ)
    (x : ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj (M.level n)).val.obj W) :
    (extensionTransition.{c, v, r} B U M (Nat.le_refl n)).val.app W x = x := by
  let η := systemScalarRestrictionUnit.{c, v, max c v r} (B.map (homOfLE (Nat.le_refl n)).op)
    (B.map_id (op n))
  have he : extensionTransition.{c, v, r} B U M (Nat.le_refl n) =
      η.inv.app ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj (M.level n)) := by
    apply extension_ext.{c, v, r} U (B.obj (op n))
    intro V y
    change (extensionTransition.{c, v, r} B U M (Nat.le_refl n)).val.app (op V.left)
        (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U (M.level n) V y) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U (M.level n) V y
    rw [extensionTransition_generator.{c, v, r}, M.identity]
  exact congrArg (fun f ↦ f.val.app W x) he

private theorem extensionTransition_compose
    (M : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U))
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (W : Cᵒᵖ)
    (x : ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj (M.level n)).val.obj W) :
    (extensionTransition.{c, v, r} B U M (h.trans k)).val.app W x =
      (extensionTransition.{c, v, r} B U M h).val.app W
        ((extensionTransition.{c, v, r} B U M k).val.app W x) := by
  have hc : B.map (homOfLE (h.trans k)).op =
      B.map (homOfLE k).op ≫ B.map (homOfLE h).op := by
    rw [← B.map_comp]
    rfl
  let η := systemScalarRestrictionComposition.{c, v, max c v r} _ _ _ hc
  have he : extensionTransition.{c, v, r} B U M (h.trans k) =
      extensionTransition.{c, v, r} B U M k ≫
        (systemRestriction.{c, v, max c v r} B k).map (extensionTransition.{c, v, r} B U M h) ≫
        η.hom.app ((localizedSystemExtension.{c, v, r} (B.obj (op l)) U).obj (M.level l)) := by
    apply extension_ext.{c, v, r} U (B.obj (op n))
    intro V y
    change (extensionTransition.{c, v, r} B U M (h.trans k)).val.app (op V.left) _ =
      (extensionTransition.{c, v, r} B U M h).val.app (op V.left)
        ((extensionTransition.{c, v, r} B U M k).val.app (op V.left)
          (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U (M.level n) V y))
    rw [extensionTransition_generator.{c, v, r}, extensionTransition_generator.{c, v, r},
      extensionTransition_generator.{c, v, r}, M.compose]
  exact congrArg (fun f ↦ f.val.app W x) he

variable
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

private theorem extensionTransition_naturality
    {M N : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U)}
    (f : M ⟶ N) {m n : ℕ} (h : m ≤ n) :
    (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map (f.app n) ≫
        extensionTransition.{c, v, r} B U N h =
      extensionTransition.{c, v, r} B U M h ≫ (systemRestriction.{c, v, max c v r} B h).map
        ((localizedSystemExtension.{c, v, r} (B.obj (op m)) U).map (f.app m)) := by
  apply extension_ext.{c, v, r} U (B.obj (op n))
  intro W x
  change (extensionTransition.{c, v, r} B U N h).val.app (op W.left)
    (((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map (f.app n)).val.app
      (op W.left) _) =
    ((localizedSystemExtension.{c, v, r} (B.obj (op m)) U).map (f.app m)).val.app
      (op W.left) ((extensionTransition.{c, v, r} B U M h).val.app (op W.left) _)
  rw [extension_map.{c, v, r}, extensionTransition_generator.{c, v, r},
    extensionTransition_generator.{c, v, r}, extension_map.{c, v, r}]
  exact congrArg (ringedSliceExtensionSection.{c, v, r} (B.obj (op m)) U (N.level m) W)
    (congrArg (fun g ↦ g.val.app (op W) x) (f.comm h))

private def extensionObject
    (M : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U)) :
    StrictRingSystem.{c, v, max c v r} B where
  level n := (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj (M.level n)
  transition := extensionTransition.{c, v, r} B U M
  identity := extensionTransition_identity.{c, v, r} B U M
  compose := extensionTransition_compose.{c, v, r} B U M

private def extensionFunctor :
    StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U) ⥤
      StrictRingSystem.{c, v, max c v r} B where
  obj := extensionObject.{c, v, r} B U
  map f :=
    { app := fun n ↦ (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map (f.app n)
      comm := extensionTransition_naturality.{c, v, r} B U f }
  map_id M := strictRingSystem_hom_ext B _ _ (fun n ↦
    (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map_id (M.level n))
  map_comp f g := strictRingSystem_hom_ext B _ _ (fun n ↦
    (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map_comp (f.app n) (g.app n))

private theorem extensionFunctor_additive : (extensionFunctor.{c, v, r} B U).Additive := by
  constructor
  intro M N f g
  apply strictRingSystem_hom_ext B
  intro n
  change (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map
      ((systemEvaluation (sliceScalarRings.{c, v, r} B U) n).map (f + g)) =
    (systemEvaluation B n).map
      ((extensionFunctor.{c, v, r} B U).map f + (extensionFunctor.{c, v, r} B U).map g)
  rw [Functor.map_add, Functor.map_add, Functor.map_add]
  rfl

/-- Direct-sum extension and module sheafification extend strict semilinear systems.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03CY
(blueprint: lem-sf-slice-system-extension-construction).

Proof: At level n apply the actual localizedSystemExtension for B_n. On the
extension presheaves send the original summand [x]_f to [t(x)]_f for each system
transition t. This is semilinear over the corresponding coefficient transition.
The common abelian sheafification of the source, and uniqueness of its extended
scalar action, factor this into a module map to the scalar restriction of the
level-m extension. Identity and composition agree on all summands because those
of t do; sheafification uniqueness extends their equality. Extend system maps
in exactly the same way. Their transition squares hold on each summand by the
original strict morphism square. Identities, composition and additivity follow
from the same direct-sum formulas and functoriality of module sheafification. -/
theorem exists_sliceSystemExtensionPresentation :
    Nonempty (SliceSystemExtensionPresentation.{c, v, r} B U) := by
  refine ⟨{
    F := extensionFunctor.{c, v, r} B U
    obj_eq := fun _ _ ↦ rfl
    map_eq := ?_
    transition_generator := ?_
    additive := extensionFunctor_additive.{c, v, r} B U }⟩
  · intro M N f n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro M m n h W x
    change (extensionTransition.{c, v, r} B U M h).val.app (op W.left)
      (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U (M.level n) W x) = _
    exact extensionTransition_generator.{c, v, r} B U M h W x

end SheafOfModules
