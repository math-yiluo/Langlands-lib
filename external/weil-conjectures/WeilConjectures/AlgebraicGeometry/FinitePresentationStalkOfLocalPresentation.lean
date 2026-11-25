/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleRestrictionStalkIso
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Finite presentation of a stalk from a supplied local presentation

Source: Stacks Project, Modules, Lemma 01CP, third paragraph; Definition 01BN.
-/

@[expose] public section

universe u
open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem unit_stalk_iso (X : RingedSpace.{u}) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X x
    ∃ e : S.obj (SheafOfModules.unit (moduleRings X)) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ (U : Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit (moduleRings X)).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
  let D := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit (moduleRings X)).val.presheaf x) ≃+ X.presheaf.stalk x :=
    (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (U : Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
      e (TopCat.Presheaf.germ (SheafOfModules.unit (moduleRings X)).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r := by
    change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : OpenNhds x)) ≫
      (preservesColimitIso A D).inv) r = _
    rw [ι_preservesColimitIso_inv]
    rfl
  let f : (RingedSpace.moduleStalkFunctor X x).obj
      (SheafOfModules.unit (moduleRings X)) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq
            (SheafOfModules.unit (moduleRings X)).val.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
          ← TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit (moduleRings X)).val.presheaf
            (homOfLE inf_le_right) x hx m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
        let m' : X.presheaf.obj (op (U ⊓ V)) :=
          (SheafOfModules.unit (moduleRings X)).val.presheaf.map
            (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
        change e (TopCat.Presheaf.germ
          (SheafOfModules.unit (moduleRings X)).val.presheaf (U ⊓ V) x hx (r' * m')) =
          X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
            (SheafOfModules.unit (moduleRings X)).val.presheaf (U ⊓ V) x hx m') :
              X.presheaf.stalk x)
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
  refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
  exact hg


private instance stalk_preserves_colimits (Y : RingedSpace.{u}) (y : Y)
    (K : Type u) [SmallCategory K] :
    PreservesColimitsOfShape K (moduleStalkFunctor Y y) := by
  classical
  let R := ((sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.sheaf)
  have : PreservesColimitsOfShape K (SheafOfModules.toSheaf.{u} R) :=
    ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 K).2.1
  have : PreservesColimitsOfShape K
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Y.carrier ⋙
        stalkFunctor AddCommGrpCat.{u} y) :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := Y.carrier) y
      ).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimitsOfShape K
      (moduleStalkFunctor Y y ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}) :=
    inferInstanceAs (PreservesColimitsOfShape K
      (SheafOfModules.toSheaf R ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y.carrier ⋙
          stalkFunctor AddCommGrpCat.{u} y)))
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u})

private theorem map_free_finitePresentation
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A : Type u} [Ring A] (S : SheafOfModules.{u} R ⥤ ModuleCat.{u} A)
    (e : S.obj (SheafOfModules.unit R) ≅ ModuleCat.of A A)
    (I : Type u) [Finite I] [PreservesColimitsOfShape (Discrete I) S] :
    Module.FinitePresentation A (S.obj (SheafOfModules.free I)) := by
  classical
  let := Fintype.ofFinite I
  let iso := PreservesCoproduct.iso S (fun _ : I ↦ SheafOfModules.unit R) ≪≫
    ModuleCat.coprodIsoDirectSum (fun _ : I ↦ S.obj (SheafOfModules.unit R))
  have : Module.FinitePresentation A (S.obj (SheafOfModules.unit R)) :=
    Module.FinitePresentation.of_equiv e.toLinearEquiv.symm
  exact Module.FinitePresentation.of_equiv
    (iso.toLinearEquiv ≪≫ₗ DirectSum.linearEquivFunOnFintype _ I _).symm

-- Elaborating the mapped cokernel unfolds the presentation and its free-module maps.
private theorem map_presentation_finitePresentation
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A : Type u} [Ring A] (S : SheafOfModules.{u} R ⥤ ModuleCat.{u} A)
    [S.PreservesZeroMorphisms] [PreservesColimitsOfShape WalkingParallelPair S]
    (e : S.obj (SheafOfModules.unit R) ≅ ModuleCat.of A A)
    (F : SheafOfModules.{u} R) (P : F.Presentation) [P.IsFinite]
    [PreservesColimitsOfShape (Discrete P.generators.I) S]
    [PreservesColimitsOfShape (Discrete P.relations.I) S] :
    Module.FinitePresentation A (S.obj F) := by
  classical
  let f := (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  let g := P.generators.π
  have hfg : f ≫ g = 0 := by simp [f, g]
  have hc : IsColimit (CokernelCofork.ofπ (S.map g)
      (by rw [← S.map_comp, hfg, S.map_zero])) :=
    CokernelCofork.mapIsColimit _ P.isColimit S
  have hsurj : Function.Surjective (S.map g).hom :=
    (ModuleCat.epi_iff_surjective _).mp (epi_of_isColimit_cofork hc)
  have hex : LinearMap.range (S.map f).hom = LinearMap.ker (S.map g).hom :=
    ((ShortComplex.mk (S.map f) (S.map g)
      (by rw [← S.map_comp, hfg, S.map_zero])).moduleCat_exact_iff_range_eq_ker).mp
        (ShortComplex.exact_of_g_is_cokernel _ hc)
  have : Module.FinitePresentation A (S.obj (SheafOfModules.free P.generators.I)) :=
    map_free_finitePresentation R S e P.generators.I
  have : Module.FinitePresentation A (S.obj (SheafOfModules.free P.relations.I)) :=
    map_free_finitePresentation R S e P.relations.I
  apply Module.finitePresentation_of_surjective (S.map g).hom hsurj
  rw [← hex]
  exact Submodule.fg_range _

-- Scalar transport and the slice equivalence unfold several nested stalk instances.
/-- A supplied finite presentation on a neighborhood makes the stalk finitely presented.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third
paragraph, the right exact source-stalk sequence; Definition 01BN.
(blueprint: lem-weil-pbc-stalk-finite-presentation-of-local-presentation)

Proof: The presentation P expresses F.over U as the cokernel of the map from
free P.relations.I to free P.generators.I, given by the relation sections and
the kernel inclusion. The neighborhoods contained in U are cofinal among the
neighborhoods of x: intersect any neighborhood with U. Hence restricting to U
leaves the stalk ring and the module stalk unchanged, with their germ actions.
The unit stalk is the regular stalk module via the forgetful-colimit
comparison; its scalar compatibility is checked on simultaneous germs.
Colimit preservation identifies the stalk of each finite free sheaf with the
finite direct sum of unit stalks, hence with the corresponding finite product.
Transport P.isColimit to a surjection from the generator free module onto F_x,
whose kernel is the image of the relation free module. This image is finitely
generated since the relation index set is finite. Apply
Module.finitePresentation_of_surjective to obtain the conclusion, and transfer
it along nonempty_moduleRestrictionStalk_iso.
An empty generator set gives the zero module; an empty relation set gives a
zero kernel. The same argument applies to the zero ring, and a pointed
neighborhood cannot be empty. No local Noetherian hypothesis is used. -/
theorem finitePresentation_stalk_of_localPresentation
    (X : RingedSpace.{u}) (F : Modules X) (x : X)
    (U : Opens X) (_hxU : x ∈ U)
    (P : (F.over U).Presentation) [P.IsFinite] :
    Module.FinitePresentation (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj F) := by
  classical
  let Y := X.restrict U.isOpenEmbedding
  let y : U := ⟨x, _hxU⟩
  let E := (U.sheafOfModulesEquivOver (moduleRings X)).functor
  let ρ := (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding y).inv.hom
  let eρ := (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding y).symm
    |>.commRingCatIsoToRingEquiv
  let T := ModuleCat.restrictScalars ρ
  have : T.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
  have : E.IsEquivalence := inferInstance
  have : E.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full E
  have : T.PreservesZeroMorphisms := inferInstance
  have : (moduleStalkFunctor Y y).PreservesZeroMorphisms :=
    moduleStalkFunctor_preservesZeroMorphisms Y y
  let S := E ⋙ moduleStalkFunctor Y y ⋙ T
  have : S.PreservesZeroMorphisms :=
    inferInstanceAs ((E ⋙ moduleStalkFunctor Y y ⋙ T).PreservesZeroMorphisms)
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (moduleRings Y)) :=
    (moduleSheaves_colimits_forgetful (moduleRings Y)).2.2.1
  have : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} Y.carrier ⋙
        stalkFunctor AddCommGrpCat.{u} y) :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := Y.carrier) y
      ).leftAdjoint_preservesColimits
      |>.preservesFiniteColimits.{0, 0}
  have : PreservesFiniteColimits (moduleStalkFunctor Y y ⋙
      forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf (moduleRings Y) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y.carrier ⋙
          stalkFunctor AddCommGrpCat.{u} y)))
  have : PreservesFiniteColimits (moduleStalkFunctor Y y) :=
    preservesFiniteColimits_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u})
  have : PreservesColimitsOfShape (Discrete P.generators.I) (moduleStalkFunctor Y y) :=
    stalk_preserves_colimits Y y (Discrete P.generators.I)
  have : PreservesColimitsOfShape (Discrete P.relations.I) (moduleStalkFunctor Y y) :=
    stalk_preserves_colimits Y y (Discrete P.relations.I)
  have : PreservesColimitsOfShape WalkingParallelPair S := by dsimp only [S]; infer_instance
  have : PreservesColimitsOfShape (Discrete P.generators.I) S := by
    dsimp only [S]; infer_instance
  have : PreservesColimitsOfShape (Discrete P.relations.I) S := by
    dsimp only [S]; infer_instance
  let eU := U.sheafOfModulesEquivOverUnit (moduleRings X)
  obtain ⟨e, he⟩ := unit_stalk_iso Y y
  let eu : S.obj (SheafOfModules.unit ((moduleRings X).over U)) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
    T.mapIso ((moduleStalkFunctor Y y).mapIso eU ≪≫ e) ≪≫
      ModuleCat.restrictScalarsIsoOfEquiv eρ
  have hfp : Module.FinitePresentation (X.presheaf.stalk x) (S.obj (F.over U)) :=
    map_presentation_finitePresentation ((moduleRings X).over U) S eu (F.over U) P
  obtain ⟨eF⟩ := nonempty_moduleRestrictionStalk_iso X F U x _hxU
  have : Module.FinitePresentation (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, _hxU⟩).inv.hom).obj
        ((moduleStalkFunctor (X.restrict U.isOpenEmbedding) ⟨x, _hxU⟩).obj
          ((U.sheafOfModulesEquivOver (moduleRings X)).functor.obj (F.over U)))) := hfp
  exact Module.FinitePresentation.of_equiv eF.toLinearEquiv

end AlgebraicGeometry.RingedSpace
