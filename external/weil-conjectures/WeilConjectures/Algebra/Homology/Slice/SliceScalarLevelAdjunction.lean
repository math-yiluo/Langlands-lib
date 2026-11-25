/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic

/-! # Scalar extension commutes with localized extension

Source: Stacks Project, Modules on Sites, Tags 0E8I, 03DI, 03CY and 03EK.
(blueprint: lem-sf-slice-scalar-adjunction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r
open CategoryTheory Opposite
open scoped ChangeOfRings
attribute [local implicit_reducible] CategoryTheory.sheafCompose

namespace SheafOfModules
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

namespace ScalarLevelProof

section ScalarHom
universe a b s
variable {D : Type a} [Category.{b} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasWeakSheafify K AddCommGrpCat.{s}]
open scoped ChangeOfRings

private abbrev ringSheaf (A : Sheaf K CommRingCat.{s}) :=
  (sheafCompose K (forget₂ CommRingCat.{s} RingCat.{s})).obj A

private noncomputable abbrev restriction
    {A S : Sheaf K CommRingCat.{s}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

private theorem tensorRestriction_tmul
    {A S : Sheaf K CommRingCat.{s}} (c : A ⟶ S) (M : SheafOfModules.{s} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{b, a, s} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
        PresheafOfModulesOfCommRing.map (R := A.obj) M.val i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{b, a, s} c M i) s m

private noncomputable def tensorToRestriction
    {A S : Sheaf K CommRingCat.{s}} (c : A ⟶ S)
    (M : SheafOfModules.{s} (ringSheaf A)) (H : SheafOfModules.{s} (ringSheaf S))
    (f : changeOfRingsPresheaf.{b, a, s} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          PresheafOfModulesOfCommRing.map (R := A.obj) M.val i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {A S : Sheaf K CommRingCat.{s}} (c : A ⟶ S)
    (M : SheafOfModules.{s} (ringSheaf A)) (H : SheafOfModules.{s} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{b, a, s} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{b, a, s} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {A S : Sheaf K CommRingCat.{s}} (c : A ⟶ S)
    (M : SheafOfModules.{s} (ringSheaf A)) (H : SheafOfModules.{s} (ringSheaf S)) :
    (changeOfRingsPresheaf.{b, a, s} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {A S : Sheaf K CommRingCat.{s}} (c : A ⟶ S)
    (M : SheafOfModules.{s} (ringSheaf A)) (H : SheafOfModules.{s} (ringSheaf S)) :
    (changeOfRings.{b, a, s} c M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

end ScalarHom

private abbrev Rings (A : Sheaf J CommRingCat.{max c v r}) :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A

private abbrev Mods (A : Sheaf J CommRingCat.{max c v r}) :=
  SheafOfModules.{max c v r} (Rings.{c, v, r} A)

private abbrev Res {A S : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ S) :=
  restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a)

private theorem pure_smul {A S : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ S)
    (M : Mods.{c, v, r} A) (W : Cᵒᵖ) (x : M.val.obj W) (b : S.obj.obj W) :
    sliceScalarPure.{c, v, r} a M W x b =
      b • sliceScalarPure.{c, v, r} a M W x 1 := by
  unfold sliceScalarPure
  erw [← map_smul]
  change _ = ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Rings.{c, v, r} S).obj)).unit.app
      (changeOfRingsPresheaf.{v, c, max c v r} a M)).app W
      ((b * 1) ⊗ₜ[A.obj.obj W, (a.hom.app W).hom] x)
  rw [mul_one]

private theorem scalar_hom {A S : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ S)
    (M : Mods.{c, v, r} A) (N : Mods.{c, v, r} S)
    (f : changeOfRings.{v, c, max c v r} a M ⟶ N) (W : Cᵒᵖ) (x : M.val.obj W) :
    (tensorHomEquiv a M N f).val.app W x =
      f.val.app W (sliceScalarPure.{c, v, r} a M W x 1) := rfl

private theorem extension_unit (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x =
      ringedSliceExtensionSection.{c, v, r} A U G W x :=
  (localizedSystemAdjunction_existsUnique.{c, v, r} A U).exists.choose_spec G (op W) x

private theorem extension_hom (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} A) (f : (localizedSystemExtension.{c, v, r} A U).obj G ⟶ N)
    (W : Over U) (x : G.val.obj (op W)) :
    (((localizedSystemAdjunction.{c, v, r} A U).homEquiv G N) f).val.app (op W) x =
      f.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x) := by
  change f.val.app (op W.left)
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x) = _
  rw [extension_unit.{c, v, r}]

section Comparison
variable (A S : Sheaf J CommRingCat.{max c v r}) (a : A ⟶ S) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

private abbrev sliceMap : A.over U ⟶ S.over U :=
  (J.overPullback CommRingCat.{max c v r} U).map a

private abbrev Src (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U)) :=
  changeOfRings.{v, c, max c v r} a ((localizedSystemExtension.{c, v, r} A U).obj G)

private abbrev Tgt (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U)) :=
  (localizedSystemExtension.{c, v, r} S U).obj
    (changeOfRings.{v, max c v, max c v r} (sliceMap.{c, v, r} A S a U) G)

private def leftHom (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} S) :
    (Src.{c, v, r} A S a U G ⟶ N) ≃ (G ⟶ ((Res.{c, v, r} a).obj N).over U) :=
  (tensorHomEquiv a _ N).trans ((localizedSystemAdjunction.{c, v, r} A U).homEquiv _ _)

private def rightHom (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} S) :
    (Tgt.{c, v, r} A S a U G ⟶ N) ≃ (G ⟶ ((Res.{c, v, r} a).obj N).over U) :=
  ((localizedSystemAdjunction.{c, v, r} S U).homEquiv _ _).trans
    (tensorHomEquiv (sliceMap.{c, v, r} A S a U) G (N.over U))

omit [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem leftHom_apply
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} S) (f : Src.{c, v, r} A S a U G ⟶ N)
    (W : Over U) (x : G.val.obj (op W)) :
    (leftHom.{c, v, r} A S a U G N f).val.app (op W) x =
      f.val.app (op W.left) (sliceScalarPure.{c, v, r} a _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) 1) := by
  exact (extension_hom.{c, v, r} A U G _ _ W x).trans (scalar_hom.{c, v, r} a _ N f _ _)

private theorem rightHom_apply
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} S) (f : Tgt.{c, v, r} A S a U G ⟶ N)
    (W : Over U) (x : G.val.obj (op W)) :
    (rightHom.{c, v, r} A S a U G N f).val.app (op W) x =
      f.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} S U _ W
        (sliceScalarPure.{max c v, v, r} (sliceMap.{c, v, r} A S a U) G (op W) x 1)) := by
  exact (scalar_hom.{max c v, v, r} (sliceMap.{c, v, r} A S a U) G _ _ _ x).trans
    (extension_hom.{c, v, r} S U _ N f W _)

private def comparisonHomEquiv
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} S) :
    (Src.{c, v, r} A S a U G ⟶ N) ≃ (Tgt.{c, v, r} A S a U G ⟶ N) :=
  (leftHom.{c, v, r} A S a U G N).trans (rightHom.{c, v, r} A S a U G N).symm

private theorem comparisonHomEquiv_naturality
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N N' : Mods.{c, v, r} S) (f : Src.{c, v, r} A S a U G ⟶ N) (g : N ⟶ N') :
    comparisonHomEquiv.{c, v, r} A S a U G N' (f ≫ g) =
      comparisonHomEquiv.{c, v, r} A S a U G N f ≫ g := by
  apply (rightHom.{c, v, r} A S a U G N').injective
  change (rightHom.{c, v, r} A S a U G N')
    ((rightHom.{c, v, r} A S a U G N').symm
      (leftHom.{c, v, r} A S a U G N' (f ≫ g))) = _
  rw [Equiv.apply_symm_apply]
  have h := (rightHom.{c, v, r} A S a U G N).apply_symm_apply (leftHom.{c, v, r} A S a U G N f)
  ext W x
  have hx := congrArg (fun k ↦ k.val.app W x) h
  simp only [leftHom_apply.{c, v, r}, rightHom_apply.{c, v, r}] at hx ⊢
  exact congrArg (fun y ↦ g.val.app (op W.unop.left) y) hx.symm

private def comparisonIso
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U)) :
    Src.{c, v, r} A S a U G ≅ Tgt.{c, v, r} A S a U G where
  hom := (comparisonHomEquiv.{c, v, r} A S a U G _).symm (𝟙 _)
  inv := comparisonHomEquiv.{c, v, r} A S a U G _ (𝟙 _)
  hom_inv_id := by
    apply (comparisonHomEquiv.{c, v, r} A S a U G _).injective
    rw [comparisonHomEquiv_naturality.{c, v, r}, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := comparisonHomEquiv_naturality.{c, v, r} A S a U G _ _
      (𝟙 (Src.{c, v, r} A S a U G)) ((comparisonHomEquiv.{c, v, r} A S a U G _).symm (𝟙 _))
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using h.symm

private theorem comparison_generator
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (W : Over U) (x : G.val.obj (op W)) (b : S.obj.obj (op W.left)) :
    (comparisonIso.{c, v, r} A S a U G).hom.val.app (op W.left)
      (sliceScalarPure.{c, v, r} a _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) b) =
      ringedSliceExtensionSection.{c, v, r} S U _ W
        (sliceScalarPure.{max c v, v, r} (sliceMap.{c, v, r} A S a U) G (op W) x b) := by
  have h := (leftHom.{c, v, r} A S a U G _).apply_symm_apply
    (rightHom.{c, v, r} A S a U G _ (𝟙 _))
  have hx := congrArg (fun k ↦ k.val.app (op W) x) h
  change (leftHom.{c, v, r} A S a U G _
    (comparisonIso.{c, v, r} A S a U G).hom).val.app (op W) x = _ at hx
  rw [leftHom_apply.{c, v, r}, rightHom_apply.{c, v, r}] at hx
  change _ = ringedSliceExtensionSection.{c, v, r} S U _ W
    (sliceScalarPure.{max c v, v, r} (sliceMap.{c, v, r} A S a U) G (op W) x 1) at hx
  rw [pure_smul.{c, v, r}, map_smul, hx]
  erw [pure_smul.{max c v, v, r} (sliceMap.{c, v, r} A S a U) G (op W) x b]
  classical
  unfold ringedSliceExtensionSection
  erw [map_smul, map_smul]

omit [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem comparison_ext
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} S) (f g : Src.{c, v, r} A S a U G ⟶ N)
    (h : ∀ (W : Over U) (x : G.val.obj (op W)),
      f.val.app (op W.left) (sliceScalarPure.{c, v, r} a _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) 1) =
      g.val.app (op W.left) (sliceScalarPure.{c, v, r} a _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) 1)) : f = g := by
  apply (leftHom.{c, v, r} A S a U G N).injective
  ext W x
  rw [leftHom_apply.{c, v, r}, leftHom_apply.{c, v, r}]
  exact h W.unop x
attribute [irreducible] tensorHomEquiv leftHom rightHom comparisonHomEquiv comparisonIso

end Comparison

end ScalarLevelProof

/-- The two orders of scalar extension and localized extension have a uniquely
normalized coefficient-linear comparison.
Source: Stacks 0E8I, via 03DI, 03CY and 03EK
(blueprint: lem-sf-slice-scalar-adjunction-comparison).
Proof: Both represented Hom functors are naturally equivalent to maps from G to
scalar restriction followed by slice restriction. Apply the equivalence and its
inverse to identity maps. Naturality proves both inverse equations. Evaluate the
transposes on an original summand to obtain the formula at coefficient 1, then
use coefficient linearity for all b. -/
theorem exists_scalarSliceAdjunctionComparison
    (A S : Sheaf J CommRingCat.{max c v r}) (a : A ⟶ S) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (G : SheafOfModules.{max c v r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U)) :
    ∃ e : changeOfRings.{v, c, max c v r} a
        ((localizedSystemExtension.{c, v, r} A U).obj G) ≅
      (localizedSystemExtension.{c, v, r} S U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((J.overPullback CommRingCat.{max c v r} U).map a) G),
      ∀ (W : Over U) (x : G.val.obj (op W)) (b : S.obj.obj (op W.left)),
        e.hom.val.app (op W.left)
          (sliceScalarPure.{c, v, r} a _ (op W.left)
            (ringedSliceExtensionSection.{c, v, r} A U G W x) b) =
          ringedSliceExtensionSection.{c, v, r} S U _ W
            (sliceScalarPure.{max c v, v, r}
              ((J.overPullback CommRingCat.{max c v r} U).map a) G (op W) x b) :=
  ⟨ScalarLevelProof.comparisonIso.{c, v, r} A S a U G,
    ScalarLevelProof.comparison_generator.{c, v, r} A S a U G⟩

/-- Unit tensors of original summands detect maps out of scalar-extended localized
extension, even though arbitrary sheaf sections need not be globally generated.
Source: Stacks 03DI, 03CY, 03EK and 0E8I
(blueprint: lem-sf-slice-scalar-adjunction-comparison).
Proof: Under the scalar adjunction followed by the localized-extension adjunction,
the transpose evaluates a morphism on precisely these unit tensors. The proposed
equality therefore gives equal transposes sectionwise. Injectivity gives equality. -/
theorem scalarSliceAdjunctionHom_ext
    (A S : Sheaf J CommRingCat.{max c v r}) (a : A ⟶ S) (U : C)
    (G : SheafOfModules.{max c v r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S))
    (f g : changeOfRings.{v, c, max c v r} a
      ((localizedSystemExtension.{c, v, r} A U).obj G) ⟶ N)
    (h : ∀ (W : Over U) (x : G.val.obj (op W)),
      f.val.app (op W.left) (sliceScalarPure.{c, v, r} a _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) 1) =
      g.val.app (op W.left) (sliceScalarPure.{c, v, r} a _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) 1)) : f = g :=
  ScalarLevelProof.comparison_ext.{c, v, r} A S a U G N f g h

end SheafOfModules
