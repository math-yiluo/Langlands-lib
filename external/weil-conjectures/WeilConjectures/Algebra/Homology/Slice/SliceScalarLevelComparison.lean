/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic
public import WeilConjectures.Algebra.Homology.Slice.SliceScalarLevelComparisonBasic
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.Algebra.Homology.Slice.SliceScalarLevelAdjunction

/-! # Coefficient-linear comparisons at each scalar level

Source: Stacks Project, Modules on Sites, Tags 0E8I, 03DI, 03CY and 03EK.
(blueprint: lem-sf-slice-scalar-level-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r
open CategoryTheory Opposite
open scoped ChangeOfRings
attribute [local implicit_reducible] CategoryTheory.sheafCompose
attribute [local irreducible] SheafOfModules.sliceScalarComponentHom

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

namespace ScalarLevelProof

private abbrev Rings (A : Sheaf J CommRingCat.{max c v r}) :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A

private abbrev Mods (A : Sheaf J CommRingCat.{max c v r}) :=
  SheafOfModules.{max c v r} (Rings.{c, v, r} A)

private abbrev Res {A S : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ S) :=
  restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a)

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

private theorem extension_ext (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    (G : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U))
    (N : Mods.{c, v, r} A) (f g : (localizedSystemExtension.{c, v, r} A U).obj G ⟶ N)
    (h : ∀ (W : Over U) (x : G.val.obj (op W)),
      f.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x) =
        g.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x)) :
    f = g := by
  apply ((localizedSystemAdjunction.{c, v, r} A U).homEquiv G N).injective
  ext W x
  exact (extension_hom.{c, v, r} A U G N f W.unop x).trans
    ((h W.unop x).trans (extension_hom.{c, v, r} A U G N g W.unop x).symm)

private theorem extension_map (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    {G G' : SheafOfModules.{max c v r} ((Rings.{c, v, r} A).over U)} (g : G ⟶ G')
    (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemExtension.{c, v, r} A U).map g).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) =
      ringedSliceExtensionSection.{c, v, r} A U G' W (g.val.app (op W) x) := by
  have h := congrArg (fun k ↦ k.val.app (op W) x)
    ((localizedSystemAdjunction.{c, v, r} A U).unit.naturality g).symm
  change ((localizedSystemExtension.{c, v, r} A U).map g).val.app (op W.left)
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x) =
      ((localizedSystemAdjunction.{c, v, r} A U).unit.app G').val.app (op W)
        (g.val.app (op W) x) at h
  simpa only [extension_unit.{c, v, r}] using h

private theorem scalar_map {A S : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ S)
    {M M' : Mods.{c, v, r} A} (f : M ⟶ M')
    (W : Cᵒᵖ) (x : M.val.obj W) (b : S.obj.obj W) :
    (changeOfRingsHom.{v, c, max c v r} a M f).val.app W
      (sliceScalarPure.{c, v, r} a M W x b) =
        sliceScalarPure.{c, v, r} a M' W (f.val.app W x) b := by
  let fp : changeOfRingsPresheaf.{v, c, max c v r} a M ⟶
      changeOfRingsPresheaf.{v, c, max c v r} a M' :=
    { app := fun V ↦ (ModuleCat.extendScalars (a.hom.app V).hom).map (f.val.app V)
      naturality := changeOfRingsHom_naturality.{v, c, max c v r} a M f }
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Rings.{c, v, r} S).obj)).unit.naturality fp
  have hx := congrArg (fun k ↦ k.app W (b ⊗ₜ[A.obj.obj W, (a.hom.app W).hom] x)) h
  change ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Rings.{c, v, r} S).obj)).unit.app
      (changeOfRingsPresheaf.{v, c, max c v r} a M')).app W
      ((ModuleCat.extendScalars (a.hom.app W).hom).map (f.val.app W)
        (b ⊗ₜ[A.obj.obj W, (a.hom.app W).hom] x)) = _ at hx
  rw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

private theorem tower_transition_cast
    (A : Sheaf J CommRingCat.{max c v r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r})
    (a : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (P : SliceScalarTowerPresentation.{c, v, r} A B a)
    (H : Mods.{c, v, r} A) {m n : ℕ} (h : m ≤ n) (W : Cᵒᵖ)
    (x : H.val.obj W) (b : (B.obj (op n)).obj.obj W) :
    ((P.F.obj H).transition h).val.app W
      ((eqToHom (P.obj_eq H n).symm).val.app W
        (sliceScalarPure.{c, v, r} (a.app (op n)) H W x b)) =
      (eqToHom (P.obj_eq H m).symm).val.app W
        (sliceScalarPure.{c, v, r} (a.app (op m)) H W x
          ((B.map (homOfLE h).op).hom.app W b)) := by
  have ht := congrArg ((eqToHom (P.obj_eq H m).symm).val.app W)
    (P.transition_pure H h W x b)
  have hi (z : ((P.F.obj H).level m).val.obj W) :
      (eqToHom (P.obj_eq H m).symm).val.app W
        ((eqToHom (P.obj_eq H m)).val.app W z) = z :=
    congrArg (fun f ↦ f.val.app W z) (eqToIso (P.obj_eq H m)).hom_inv_id
  exact (hi _).symm.trans ht

private theorem tower_map_cast
    (A : Sheaf J CommRingCat.{max c v r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r})
    (a : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (P : SliceScalarTowerPresentation.{c, v, r} A B a)
    {H H' : Mods.{c, v, r} A} (f : H ⟶ H') (n : ℕ) (W : Cᵒᵖ)
    (x : H.val.obj W) (b : (B.obj (op n)).obj.obj W) :
    ((P.F.map f).app n).val.app W
      ((eqToHom (P.obj_eq H n).symm).val.app W
        (sliceScalarPure.{c, v, r} (a.app (op n)) H W x b)) =
      (eqToHom (P.obj_eq H' n).symm).val.app W
        (sliceScalarPure.{c, v, r} (a.app (op n)) H' W (f.val.app W x) b) := by
  rw [P.map_eq]
  simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  change (eqToHom (P.obj_eq H' n).symm).val.app W
    ((changeOfRingsHom.{v, c, max c v r} (a.app (op n)) H f).val.app W _) = _
  rw [scalar_map.{c, v, r}]
  rfl

end ScalarLevelProof

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})
  (α : (Functor.const ℕᵒᵖ).obj O ⟶ B)
  (AX : SliceScalarTowerPresentation.{c, v, r} O B α)
  (AV : SliceScalarTowerPresentation.{max c v, v, r} (O.over U)
    (sliceScalarRings.{c, v, r} B U) (sliceScalarAlgebra.{c, v, r} B U O α))
  (extension : SliceSystemExtensionPresentation.{c, v, r} B U)

private def levelComparisonIso (G) (n : ℕ) :
    changeOfRings.{v, c, max c v r} (α.app (op n))
      ((localizedSystemExtension.{c, v, r} O U).obj G) ≅
    (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
      (changeOfRings.{v, max c v, max c v r}
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G) :=
  (exists_scalarSliceAdjunctionComparison.{c, v, r}
    O (B.obj (op n)) (α.app (op n)) U G).choose

private theorem levelComparison_generator (G) (n : ℕ) (W : Over U)
    (x : G.val.obj (op W)) (b : (B.obj (op n)).obj.obj (op W.left)) :
    (levelComparisonIso.{c, v, r} B U O α G n).hom.val.app (op W.left)
      (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} O U G W x) b) =
    ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U _ W
      (sliceScalarPure.{max c v, v, r}
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b) :=
  (exists_scalarSliceAdjunctionComparison.{c, v, r}
    O (B.obj (op n)) (α.app (op n)) U G).choose_spec W x b

attribute [irreducible] levelComparisonIso

private theorem transported_generator (G) (n : ℕ) (W : Over U)
    (x : G.val.obj (op W)) (b : (B.obj (op n)).obj.obj (op W.left)) :
    (eqToHom (extension.obj_eq (AV.F.obj G) n)).val.app (op W.left)
      ((sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
        (levelComparisonIso.{c, v, r} B U O α) G n).val.app (op W.left)
          ((eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n).symm).val.app
            (op W.left) (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
              (ringedSliceExtensionSection.{c, v, r} O U G W x) b))) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U ((AV.F.obj G).level n) W
        ((eqToHom (AV.obj_eq G n).symm).val.app (op W)
          (sliceScalarPure.{max c v, v, r}
            ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b)) := by
  simp only [sliceScalarComponentHom, ← ModuleCat.comp_apply,
    ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map
    (eqToHom (AV.obj_eq G n).symm)).val.app (op W.left)
      ((levelComparisonIso.{c, v, r} B U O α G n).hom.val.app (op W.left) _) = _
  rw [levelComparison_generator.{c, v, r}, ScalarLevelProof.extension_map.{c, v, r}]
  rfl

private theorem transported_generator_inv (G) (n : ℕ) (W : Over U)
    (x : G.val.obj (op W)) (b : (B.obj (op n)).obj.obj (op W.left)) :
    (sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
      (levelComparisonIso.{c, v, r} B U O α) G n).val.app (op W.left)
        ((eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n).symm).val.app
          (op W.left) (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
            (ringedSliceExtensionSection.{c, v, r} O U G W x) b)) =
      (eqToHom (extension.obj_eq (AV.F.obj G) n).symm).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U ((AV.F.obj G).level n) W
          ((eqToHom (AV.obj_eq G n).symm).val.app (op W)
            (sliceScalarPure.{max c v, v, r}
              ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b))) := by
  have h := congrArg ((eqToHom (extension.obj_eq (AV.F.obj G) n).symm).val.app (op W.left))
    (transported_generator.{c, v, r} B U O α AX AV extension G n W x b)
  simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using h

private theorem comparison_transition (G) {m n : ℕ} (h : m ≤ n) :
    sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
        (levelComparisonIso.{c, v, r} B U O α) G n ≫
      (extension.F.obj (AV.F.obj G)).transition h =
    (AX.F.obj ((localizedSystemExtension.{c, v, r} O U).obj G)).transition h ≫
      (systemRestriction.{c, v, max c v r} B h).map
        (sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
          (levelComparisonIso.{c, v, r} B U O α) G m) := by
  apply (Iso.cancel_iso_inv_left
    (eqToIso (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n)) _ _).mp
  apply (Iso.cancel_iso_hom_right _ _
    ((systemRestriction.{c, v, max c v r} B h).mapIso
      (eqToIso (extension.obj_eq (AV.F.obj G) m)))).mp
  apply scalarSliceAdjunctionHom_ext.{c, v, r} O (B.obj (op n)) (α.app (op n)) U G
  intro W x
  change (eqToHom (extension.obj_eq (AV.F.obj G) m)).val.app (op W.left)
    (((extension.F.obj (AV.F.obj G)).transition h).val.app (op W.left)
      ((sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
        (levelComparisonIso.{c, v, r} B U O α) G n).val.app (op W.left)
          ((eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n).symm).val.app
            (op W.left) (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
              (ringedSliceExtensionSection.{c, v, r} O U G W x) 1)))) = _
  rw [transported_generator_inv.{c, v, r}, extension.transition_generator,
    ScalarLevelProof.tower_transition_cast.{max c v, v, r}]
  change _ = (eqToHom (extension.obj_eq (AV.F.obj G) m)).val.app (op W.left)
    ((sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
      (levelComparisonIso.{c, v, r} B U O α) G m).val.app (op W.left)
        (((AX.F.obj ((localizedSystemExtension.{c, v, r} O U).obj G)).transition h).val.app
          (op W.left)
            ((eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n).symm).val.app
              (op W.left) (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
                (ringedSliceExtensionSection.{c, v, r} O U G W x) 1))))
  rw [ScalarLevelProof.tower_transition_cast.{c, v, r}, transported_generator.{c, v, r}]
  simp only [map_one]

private theorem comparison_naturality {G G'} (g : G ⟶ G') (n : ℕ) :
    (AX.F.map ((localizedSystemExtension.{c, v, r} O U).map g)).app n ≫
      sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
        (levelComparisonIso.{c, v, r} B U O α) G' n =
    sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
        (levelComparisonIso.{c, v, r} B U O α) G n ≫
      (extension.F.map (AV.F.map g)).app n := by
  apply (Iso.cancel_iso_inv_left
    (eqToIso (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n)) _ _).mp
  apply (Iso.cancel_iso_hom_right _ _
    (eqToIso (extension.obj_eq (AV.F.obj G') n))).mp
  apply scalarSliceAdjunctionHom_ext.{c, v, r} O (B.obj (op n)) (α.app (op n)) U G
  intro W x
  change (eqToHom (extension.obj_eq (AV.F.obj G') n)).val.app (op W.left)
    ((sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
      (levelComparisonIso.{c, v, r} B U O α) G' n).val.app (op W.left)
        (((AX.F.map ((localizedSystemExtension.{c, v, r} O U).map g)).app n).val.app
          (op W.left) ((eqToHom
            (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n).symm).val.app
              (op W.left) (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
                (ringedSliceExtensionSection.{c, v, r} O U G W x) 1)))) = _
  rw [ScalarLevelProof.tower_map_cast.{c, v, r}, ScalarLevelProof.extension_map.{c, v, r},
    transported_generator.{c, v, r}]
  rw [extension.map_eq]
  change _ = (eqToHom (extension.obj_eq (AV.F.obj G') n)).val.app (op W.left)
    ((eqToHom (extension.obj_eq (AV.F.obj G') n).symm).val.app (op W.left)
      (((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map
        ((AV.F.map g).app n)).val.app (op W.left)
          ((eqToHom (extension.obj_eq (AV.F.obj G) n)).val.app (op W.left)
            ((sliceScalarComponentHom.{c, v, r} B U O α AX AV extension
              (levelComparisonIso.{c, v, r} B U O α) G n).val.app (op W.left)
                ((eqToHom
                  (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n).symm).val.app
                    (op W.left) (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
                      (ringedSliceExtensionSection.{c, v, r} O U G W x) 1))))))
  rw [transported_generator.{c, v, r}, ScalarLevelProof.extension_map.{c, v, r}]
  have hm := ScalarLevelProof.tower_map_cast.{max c v, v, r}
    (O.over U) (sliceScalarRings.{c, v, r} B U)
    (sliceScalarAlgebra.{c, v, r} B U O α) AV g n (op W) x 1
  have hi (y : ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
      ((AV.F.obj G').level n)).val.obj (op W.left)) :
      (eqToHom (extension.obj_eq (AV.F.obj G') n)).val.app (op W.left)
        ((eqToHom (extension.obj_eq (AV.F.obj G') n).symm).val.app (op W.left) y) = y :=
    congrArg (fun f ↦ f.val.app (op W.left) y)
      (eqToIso (extension.obj_eq (AV.F.obj G') n)).inv_hom_id
  exact (congrArg (fun y ↦ ringedSliceExtensionSection.{c, v, r}
    (B.obj (op n)) U ((AV.F.obj G').level n) W y) hm).symm.trans (hi _).symm

/-- The scalar-linear level comparison exists for the prescribed tower presentations.
Source: Stacks 0E8I, 03DI, 03CY, 03EK and Sites 00WK; coefficient refinement of
lem-sf-semilinear-slice-scalar-generators, steps 1--6
(blueprint: lem-sf-slice-scalar-level-comparison).

Proof: The normalized coefficient adjunction followed by the normalized slice-extension
adjunction identifies maps from B_n tensor j_!G to N with maps from G to the slice of
Res N. Applying these adjunctions in the opposite order gives the same Hom set for
j_!(B_n|_U tensor G). The resulting natural Hom equivalence gives mutually inverse
coefficient-linear comparison maps. Evaluating the transposes on an original summand
proves the generator formula at coefficient 1; linearity gives every coefficient b.
Injectivity of the Hom equivalence proves uniqueness. The already proved scalar/slice
comparison, inverted, gives scalarIdentification and its generator equation; the
slice-extension adjunction proves its uniqueness. For transition and naturality,
cancel the prescribed object transports and use the injective Hom equivalence again.
The presentation equations and naturality of both sheafification and slice-extension
units give identical images of every unit tensor in every original summand. This
argument uses arbitrary unital algebra maps and does not require global generation
or flatness. -/
theorem exists_sliceScalarLevelComparison :
    Nonempty (SliceScalarLevelComparison.{c, v, r} B U O α AX AV extension) := by
  classical
  have sc (n : ℕ) : ∃ e : ∀ F,
      (localizedSystemExtension.{c, v, r} O U).obj
        ((ScalarLevelProof.Res.{max c v, v, r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n))).obj F) ≅
      (ScalarLevelProof.Res.{c, v, r} (α.app (op n))).obj
        ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj F),
      ∀ F (W : Over U) (x : F.val.obj (op W)),
        (e F).hom.val.app (op W.left)
          (ringedSliceExtensionSection.{c, v, r} O U _ W x) =
        ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x := by
    obtain ⟨_, _, e, he, _, _⟩ :=
      RingedOpenScalar.comparison.{c, v, r, max c v r} U (α.app (op n))
    refine ⟨fun F ↦ (e.app F).symm, ?_⟩
    intro F W x
    have h := congrArg (fun f ↦ f.val.app (op W.left)
      (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x))
        (Iso.hom_inv_id_app e F)
    change (e.inv.app F).val.app (op W.left)
      ((e.hom.app F).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x)) = _ at h
    have hx := he F (op W.left) W.hom x
    change (e.hom.app F).val.app (op W.left)
      (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x) =
        ringedSliceExtensionSection.{c, v, r} O U _ W x at hx
    rw [hx] at h
    exact h
  choose si hsi using sc
  refine ⟨{
    component := levelComparisonIso.{c, v, r} B U O α
    generator := levelComparison_generator.{c, v, r} B U O α
    unique := ?_
    scalarIdentification := si
    scalarIdentification_generator := hsi
    scalarIdentification_unique := ?_
    transition := comparison_transition.{c, v, r} B U O α AX AV extension
    naturality := comparison_naturality.{c, v, r} B U O α AX AV extension }⟩
  · intro G n f hf
    apply scalarSliceAdjunctionHom_ext.{c, v, r} O (B.obj (op n)) (α.app (op n)) U G
    intro W x
    exact (hf W x 1).trans (levelComparison_generator.{c, v, r} B U O α G n W x 1).symm
  · intro n F f hf
    apply ScalarLevelProof.extension_ext.{c, v, r} O U
    intro W x
    exact (hf W x).trans (hsi n F W x).symm

end SheafOfModules
