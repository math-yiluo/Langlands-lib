/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Normalized scalar inverse-image composition

Source: Stacks Project, Sheaves, Tags 008I and 0097.
(blueprint: lem-sc-scalar-inverse-image-composition-coherence).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Composition of inverse images, normalized by their adjunction units.
Source: Stacks Project, Tag 008I, lemma-pullback-composition.
(blueprint: lem-sc-scalar-inverse-image-composition-coherence). -/
def scalarInverseImageCompIso (k : Type w) [Field k]
    {A B C : Scheme.{w}} (a : A ⟶ B) (b : B ⟶ C) :
    scalarInverseImage (k := k) (a ≫ b) ≅
      scalarInverseImage (k := k) b ⋙ scalarInverseImage (k := k) a :=
  ((TopologicalSpace.Opens.map (a ≫ b).base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) _ _).leftAdjointUniq
    (((TopologicalSpace.Opens.map b.base).sheafAdjunctionContinuous (ModuleCat.{w} k) _ _).comp
      ((TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k) _ _))

attribute [local instance] Sheaf.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homEquiv_unique {D E : Type*} [Category* D] [Category* E]
    {L L' : D ⥤ E} {R : E ⥤ D} (u : L ⊣ R) (v : L' ⊣ R)
    (X : D) (Y : E) (t : L'.obj X ⟶ Y) :
    u.homEquiv X Y ((u.leftAdjointUniq v).hom.app X ≫ t) = v.homEquiv X Y t := by
  rw [u.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    v.homEquiv_unit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constant_homEquiv (k : Type w) [Field k]
    {X Y : Scheme.{w}} (t : Y ⟶ X) (M : ModuleCat.{w} k) :
    (constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{w} k)
      Limits.isTerminalTop).homEquiv
      _ _ (((TopologicalSpace.Opens.map t.base).sheafAdjunctionContinuous
        (ModuleCat.{w} k) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv
          _ _ (((TopologicalSpace.Opens.map t.base).constantSheafsheafPullbackIso
            (ModuleCat.{w} k) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
            Limits.isTerminalTop Limits.isTerminalTop).hom.app M)) =
      (constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{w} k)
        Limits.isTerminalTop).unit.app
        M := by
  let cX := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{w} k) Limits.isTerminalTop
  let cY := constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{w} k) Limits.isTerminalTop
  let adt := (TopologicalSpace.Opens.map t.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let ev := (TopologicalSpace.Opens.map t.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (Opposite.op ⊤)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((cX.comp adt).ofNatIsoRight ev) cY M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  erw [Equiv.trans_apply] at h
  change _ ≫ 𝟙 _ = _ at h
  rw [Category.comp_id] at h
  exact h

-- Prove constant-unit coherence separately from coefficient coherence.
private theorem scalarInverseImageCompIso_unit (k : Type w) [Field k]
    {A B C : Scheme.{w}} (a : A ⟶ B) (b : B ⟶ C) :
    (scalarInverseUnitIso (a ≫ b)).inv ≫
        (scalarInverseImageCompIso k a b).hom.app (𝟙_ (KSheaf C k)) =
      (scalarInverseUnitIso a).inv ≫
        (scalarInverseImage a).map (scalarInverseUnitIso b).inv := by
  let eA := ((TopologicalSpace.Opens.map a.base).constantSheafsheafPullbackIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
    Limits.isTerminalTop Limits.isTerminalTop).app (ModuleCat.of k k)
  let eB := ((TopologicalSpace.Opens.map b.base).constantSheafsheafPullbackIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology C) (Opens.grothendieckTopology B)
    Limits.isTerminalTop Limits.isTerminalTop).app (ModuleCat.of k k)
  let eC := ((TopologicalSpace.Opens.map (a ≫ b).base).constantSheafsheafPullbackIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology C) (Opens.grothendieckTopology A)
    Limits.isTerminalTop Limits.isTerminalTop).app (ModuleCat.of k k)
  unfold scalarInverseUnitIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
  change constantScalarUnitIso.inv ≫ eC.inv ≫
    (scalarInverseImage (a ≫ b)).map constantScalarUnitIso.hom ≫
      (scalarInverseImageCompIso k a b).hom.app _ =
    constantScalarUnitIso.inv ≫ eA.inv ≫
      (scalarInverseImage a).map constantScalarUnitIso.hom ≫
        (scalarInverseImage a).map
          (constantScalarUnitIso.inv ≫ eB.inv ≫
            (scalarInverseImage b).map constantScalarUnitIso.hom)
  rw [(scalarInverseImageCompIso k a b).hom.naturality]
  simp only [Functor.comp_map, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← cancel_epi constantScalarUnitIso.hom]
  simp only [Iso.hom_inv_id_assoc]
  simp only [← Category.assoc]
  apply congrArg (fun t ↦ t ≫ (scalarInverseImage a).map
    ((scalarInverseImage b).map constantScalarUnitIso.hom))
  rw [← cancel_epi eC.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← cancel_mono ((scalarInverseImage a).mapIso eB).hom]
  rw [← cancel_mono eA.hom]
  simp only [Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  let cC := constantSheafAdj (Opens.grothendieckTopology C) (ModuleCat.{w} k)
    Limits.isTerminalTop
  let ac := (TopologicalSpace.Opens.map (a ≫ b).base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology C) (Opens.grothendieckTopology A)
  let aa := (TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
  let ab := (TopologicalSpace.Opens.map b.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology C) (Opens.grothendieckTopology B)
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  apply ((cC.comp ac).homEquiv _ _).injective
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.trans_apply]
  unfold scalarInverseImageCompIso
  erw [homEquiv_unique ac (ab.comp aa) _ _
    ((scalarInverseImage a).map eB.hom ≫ eA.hom)]
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, aa.homEquiv_naturality_left eB.hom eA.hom]
  rw [ab.homEquiv_naturality_right, cC.homEquiv_naturality_right]
  erw [constant_homEquiv k b (ModuleCat.of k k), constant_homEquiv k (a ≫ b)
    (ModuleCat.of k k)]
  change (constantSheafAdj (Opens.grothendieckTopology B) (ModuleCat.{w} k)
    Limits.isTerminalTop).unit.app (ModuleCat.of k k) ≫
      ((sheafSections (Opens.grothendieckTopology B) (ModuleCat.{w} k)).obj (Opposite.op ⊤)).map
        (aa.homEquiv _ _ eA.hom) = _
  erw [← (constantSheafAdj (Opens.grothendieckTopology B) (ModuleCat.{w} k)
    Limits.isTerminalTop).homEquiv_unit]
  exact constant_homEquiv k a (ModuleCat.of k k)

private theorem scalarInverseImageCompIso_coefficient
    (k : Type w) [Field k] (A B C : Scheme.{w})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (fC : C ⟶ Spec (CommRingCat.of k)) (a : A ⟶ B) (b : B ⟶ C)
    (ha : a ≫ fB = fA) (hb : b ≫ fC = fB) (F : C.Modules) :
    (scalarInverseImageCompIso k a b).hom.app (scalarSheaf fC F) ≫
        (scalarInverseImage a).map (scalarPullbackCoefficient fC fB b hb F) ≫
        scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F) ≫
        scalarHom fA ((scalarPullbackCompIso a b).app F).inv =
      scalarPullbackCoefficient fC fA (a ≫ b)
        (by rw [Category.assoc, hb, ha]) F := by
  let adj := (TopologicalSpace.Opens.map (a ≫ b).base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology C) (Opens.grothendieckTopology A)
  let aa := (TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
  let ab := (TopologicalSpace.Opens.map b.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology C) (Opens.grothendieckTopology B)
  apply (adj.homEquiv _ _).injective
  unfold scalarInverseImageCompIso
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  erw [aa.homEquiv_naturality_left (scalarPullbackCoefficient fC fB b hb F)
    (scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F) ≫
      scalarHom fA ((scalarPullbackCompIso a b).app F).inv)]
  rw [ab.homEquiv_naturality_right, aa.homEquiv_naturality_right]
  ext U s
  change ((scalarPullbackCompIso a b).app F).inv.val.app
      (Opposite.op (a ⁻¹ᵁ (b ⁻¹ᵁ U.unop)))
      (((aa.homEquiv _ _)
        (scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F))).hom.app
          (Opposite.op (b ⁻¹ᵁ U.unop))
        (((ab.homEquiv _ _) (scalarPullbackCoefficient fC fB b hb F)).hom.app U s)) =
    (((adj.homEquiv _ _)
      (scalarPullbackCoefficient fC fA (a ≫ b) (by rw [Category.assoc, hb, ha]) F)).hom.app
        U s)
  have hj := fun {X Y : Scheme.{w}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (t : Y ⟶ X) (h : t ≫ f = g)
    (M : X.Modules) (V : X.Opens) (x : M.val.obj (Opposite.op V)) ↦
    Classical.choose_spec (exists_scalarPullbackCoefficient f g t h M) V x
  simp only [scalarPullbackCoefficient] at *
  rw [hj fC fB b hb F U.unop s,
    hj fB fA a ha ((tensorPullback b).obj F),
    hj fC fA (a ≫ b) (by rw [Category.assoc, hb, ha]) F]
  let tcomp := ((scalarPullbackAdjunction b).comp (scalarPullbackAdjunction a)).ofNatIsoRight
    (pushforwardComp a b)
  have ht := tcomp.unit_leftAdjointUniq_hom_app (scalarPullbackAdjunction (a ≫ b)) F
  rw [← Adjunction.leftAdjointUniq_inv_app] at ht
  dsimp only [tcomp, Adjunction.ofNatIsoRight, NatTrans.comp_app,
    Functor.whiskerLeft_app] at ht
  rw [Adjunction.comp_unit_app] at ht
  have ht' := congrArg (fun m ↦ m.val.app U s) ht
  unfold scalarPullbackCompIso
  change (((scalarPullbackAdjunction (a ≫ b)).leftAdjointUniq tcomp).inv.app F).val.app
    (Opposite.op (a ⁻¹ᵁ b ⁻¹ᵁ U.unop))
      (((scalarPullbackAdjunction a).unit.app ((tensorPullback b).obj F)).val.app
        (Opposite.op (b ⁻¹ᵁ U.unop))
        (((scalarPullbackAdjunction b).unit.app F).val.app U s)) =
    ((scalarPullbackAdjunction (a ≫ b)).unit.app F).val.app U s at ht'
  simpa only [scalarPullbackAdjunction, tcomp, Iso.app_inv] using ht'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The two coherence computations unfold several composed sheaf adjunctions.
/-- The normalized inverse-image comparison respects constant units and module coefficients.
Source: Stacks Project, Tags 008I and 0097, composition of pullback adjunctions.
(blueprint: lem-sc-scalar-inverse-image-composition-coherence).

Proof: The comparison of left adjoints identifies the composite adjunction unit with the
successive units. For the first equality, use the constant-sheaf adjunction: each side
is adjoint to the map sending a constant scalar to the same scalar section. Naturality
of the constant-sheaf comparison and the unit identity therefore identify them.
For the second equality, apply the inverse-image hom equivalence and evaluate on every
open set and every section of F. The characterization of scalarPullbackCoefficient
replaces each adjoint by the tensor-pullback unit. The defining left-adjoint uniqueness
identity for scalarPullbackCompIso identifies the successive tensor units with the
composite tensor unit. The inverse-image comparison has the identical unit identity.
Thus both adjoints have equal components, and sheaf morphism extensionality and the
injectivity of the hom equivalence give the second equality. These arguments apply to
zero coefficients, empty schemes and identity arrows without cancellation of sections.
-/
theorem scalarInverseImageCompIso_coherence
    (k : Type w) [Field k] (A B C : Scheme.{w})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (fC : C ⟶ Spec (CommRingCat.of k)) (a : A ⟶ B) (b : B ⟶ C)
    (ha : a ≫ fB = fA) (hb : b ≫ fC = fB) (F : C.Modules) :
    (scalarInverseUnitIso (a ≫ b)).inv ≫
        (scalarInverseImageCompIso k a b).hom.app (𝟙_ (KSheaf C k)) =
      (scalarInverseUnitIso a).inv ≫
        (scalarInverseImage a).map (scalarInverseUnitIso b).inv ∧
    (scalarInverseImageCompIso k a b).hom.app (scalarSheaf fC F) ≫
        (scalarInverseImage a).map (scalarPullbackCoefficient fC fB b hb F) ≫
        scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F) ≫
        scalarHom fA ((scalarPullbackCompIso a b).app F).inv =
      scalarPullbackCoefficient fC fA (a ≫ b)
        (by rw [Category.assoc, hb, ha]) F := by
  exact ⟨scalarInverseImageCompIso_unit k a b,
    scalarInverseImageCompIso_coefficient k A B C fA fB fC a b ha hb F⟩

end
end AlgebraicGeometry.Scheme.Modules
