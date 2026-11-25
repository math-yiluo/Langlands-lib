/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Stalks of the open-extension counit

Source: Stacks Project, Sheaves, Tag 00A7, clauses (2)--(4).
(blueprint: lem-sc-open-extension-counit-stalk)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

/-- The counit of any left adjoint to open restriction is an isomorphism on
stalks inside the open, and its source has zero stalks outside the open.
Source: Stacks Project, Sheaves, Tag 00A7, clauses (2)--(4).
(blueprint: lem-sc-open-extension-counit-stalk)

Proof: Restriction has a right adjoint (direct image) whose counit is invertible:
the forgetful functor from opens over W is fully faithful, so its adjunction unit
is invertible, and the direct-image counit restricts along that unit sectionwise.
The adjoint-triple criterion makes the unit of the specified adjunction a invertible.
Its right triangle identity therefore makes the restricted counit invertible.
At an inside point, evaluate this restricted map on the image opens of W and apply
the abelian stalk functor. The restriction-stalk comparison isomorphisms conjugate
this map to the global counit stalk map, as checked on germs. Hence that map is
invertible, without identifying the specified adjunction with a canonical one.

Outside W, use localizedModule_adjunction_exact to obtain the canonical left
adjoint, the direct-sum extension presheaf followed by module sheafification.
A neighborhood containing x has no arrow to W; its direct sum is zero. Every
presheaf stalk element is represented by such a section, hence is zero. The
sheafification unit induces a stalk isomorphism, so the sheafified stalk is zero.
Uniqueness of left adjoints supplies an isomorphism from S to this construction;
apply the abelian stalk functor and transport the zero-object property. No covering
hypothesis is used. The empty and whole-space opens require no exceptions. -/
theorem open_extension_counit_stalk (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (_hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (W : Opens X)
    (S : SheafOfModules.{u} (R.over W) ⥤ SheafOfModules.{u} R)
    (a : S ⊣ overFunctor.{u} R W) (F : SheafOfModules.{u} R) (x : X) :
    let T := toSheaf R ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    (x ∈ W → IsIso (T.map (a.counit.app F))) ∧
      (x ∉ W → IsZero (T.obj (S.obj ((overFunctor.{u} R W).obj F)))) := by
  classical
  let T := toSheaf R ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  -- Restriction is also left adjoint to direct image, whose counit is invertible.
  let b := SheafOfModules.overPushforwardOverAdj (R := R) W
  have : (Over.forget W).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (Subsingleton.elim _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar W).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar W).unit.app V.unop).op)
    infer_instance
  let t : Adjunction.Triple _ _ _ := ⟨a, b⟩
  have : IsIso a.unit := t.isIso_unit_iff_isIso_counit.mpr inferInstance
  have hr : IsIso ((overFunctor R W).map (a.counit.app F)) := by
    have he : (overFunctor R W).map (a.counit.app F) =
        inv (a.unit.app ((overFunctor R W).obj F)) := by
      apply (cancel_epi (a.unit.app _)).mp
      rw [a.right_triangle_components, IsIso.hom_inv_id]
      rfl
    rw [he]
    infer_instance
  refine ⟨?_, ?_⟩
  · intro hx
    let E := S.obj ((overFunctor R W).obj F)
    let A : AlgebraicGeometry.PresheafedSpace AddCommGrpCat.{u} :=
      ⟨X.carrier, E.val.presheaf⟩
    let B : AlgebraicGeometry.PresheafedSpace AddCommGrpCat.{u} :=
      ⟨X.carrier, F.val.presheaf⟩
    let f := Functor.whiskerLeft W.isOpenEmbedding.functor.op
      ((PresheafOfModules.toPresheaf _).map (a.counit.app F).val)
    have hf (V : (Opens W)ᵒᵖ) : IsIso (f.app V) := by
      let U := W.isOpenEmbedding.functor.obj V.unop
      let j : U ⟶ W := homOfLE (Set.image_subset_iff.2 (fun y _ ↦ y.2))
      have : IsIso (((SheafOfModules.forget (R.over W) ⋙
          PresheafOfModules.toPresheaf (R.over W).obj).map
          ((overFunctor R W).map (a.counit.app F))).app (Opposite.op (Over.mk j))) := by
        infer_instance
      exact this
    have : IsIso f := NatIso.isIso_of_isIso_app f
    let c := A.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩
    let d := B.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩
    have he : (TopCat.Presheaf.stalkFunctor (X := TopCat.of W)
        AddCommGrpCat.{u} ⟨x, hx⟩).map f ≫
        d.hom = c.hom ≫ T.map (a.counit.app F) := by
      apply TopCat.Presheaf.stalk_hom_ext
        (A.restrict W.isOpenEmbedding).presheaf
      intro V hV
      rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
      erw [B.restrictStalkIso_hom_eq_germ W.isOpenEmbedding V ⟨x, hx⟩ hV]
      rw [← Category.assoc]
      erw [A.restrictStalkIso_hom_eq_germ W.isOpenEmbedding V ⟨x, hx⟩ hV]
      change _ = _ ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map (a.counit.app F).val)
      erw [TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    have : IsIso (c.hom ≫ T.map (a.counit.app F)) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_left c.hom _
  · intro hx
    subst R
    have hJ : (Opens.grothendieckTopology X).toPrecoverage.toGrothendieck =
        Opens.grothendieckTopology X := by
      apply le_antisymm
      · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
      · intro V Z hZ
        simpa only [Sieve.generate_sieve] using
          Precoverage.generate_mem_toGrothendieck
            ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ Z).mpr hZ)
    let R := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
    let L := extensionByZeroPresheaf.{u} R W ⋙
      PresheafOfModules.sheafification.{u} (𝟙 R.obj)
    have ha : Nonempty (L ⊣ overFunctor.{u} R W) := by
      let P (J : GrothendieckTopology (Opens X)) (O : Sheaf J CommRingCat.{u}) :=
        let R' := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
        Nonempty (extensionByZeroPresheaf.{u} R' W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 R'.obj) ⊣ overFunctor.{u} R' W)
      change P (Opens.grothendieckTopology X) X.sheaf
      have hh : ∀ O, P (Opens.grothendieckTopology X) O := by
        rw [← hJ]
        intro O
        exact (localizedModule_adjunction_exact
          (Opens.grothendieckTopology X).toPrecoverage O W).2.2.2.2
      exact hh X.sheaf
    let a₀ := Classical.choice ha
    let G := (overFunctor R W).obj F
    let P := (extensionByZeroPresheaf.{u} R W).obj G
    have hp : IsZero (TopCat.Presheaf.stalk
        (C := AddCommGrpCat.{u}) (X := X.carrier) P.presheaf x) := by
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      suffices hh : ∀ s : TopCat.Presheaf.stalk
          (C := AddCommGrpCat.{u}) (X := X.carrier) P.presheaf x, s = 0 from
        ⟨fun s t ↦ (hh s).trans (hh t).symm⟩
      intro s
      obtain ⟨V, hxV, s, rfl⟩ :=
        TopCat.Presheaf.exists_germ_eq (X := X.carrier) P.presheaf s
      have : IsEmpty (V ⟶ W) := ⟨fun f ↦ hx (f.le hxV)⟩
      have hs : s = 0 := by
        change extensionByZeroPresheafSection R W G (Opposite.op V) at s
        exact (extensionByZeroPresheafSection_isEmpty R W G (Opposite.op V)).elim s 0
      rw [hs]
      exact map_zero _
    have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat.{u} P.presheaf
    have hL : IsZero (T.obj (L.obj G)) :=
      hp.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) P.presheaf))).symm
    exact hL.of_iso (T.mapIso ((a.leftAdjointUniq a₀).app G))

end SheafOfModules
