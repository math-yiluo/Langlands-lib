/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent

/-! # Finite type from a coherent open cover

Source: Stacks Project, Modules, Definitions 01BV and 01B5.
(blueprint: lem-weil-pbc-coherent-module-finite-type-local-cover)

Finite local generators on the open subschemes are transported to the corresponding
slice sites and assembled into local-generators data on the ambient scheme.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

-- Restriction along a scheme isomorphism gives an equivalence of module categories.
private noncomputable def restrictionEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor s.hom)
    (Scheme.Modules.restrictFunctor s.inv)
    ((Scheme.Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId)

set_option backward.isDefEq.respectTransparency false in
-- Transfer a finite generating family from an open of an open subscheme to its image.
-- The site equivalences preserve the structure module and coproducts, hence free modules.
private theorem transportGenerators (X : Scheme.{u}) (F : X.Modules)
    (W : X.Opens) (V : W.toScheme.Opens)
    (G : (((Scheme.Modules.restrictFunctor W.ι).obj F).over V).GeneratingSections)
    [G.IsFiniteType] :
    ∃ G' : (F.over (W.ι ''ᵁ V)).GeneratingSections, G'.IsFiniteType := by
  let U : X.Opens := W.ι ''ᵁ V
  let s : V.toScheme ≅ U.toScheme := W.ι.isoImage V
  let E := ((Scheme.Modules.overEquiv U).trans (restrictionEquivalence s)).trans
    (Scheme.Modules.overEquiv V).symm
  let T := E.functor
  have : T.IsEquivalence := E.isEquivalence_functor
  let eF : T.obj (F.over U) ≅ ((Scheme.Modules.restrictFunctor W.ι).obj F).over V :=
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.restrictFunctor s.hom).mapIso ((Scheme.Modules.overFunctorEquiv U).app F) ≪≫
        ((Scheme.Modules.restrictFunctorComp s.hom U.ι).app F).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (W.ι.isoImage_hom_ι V)).app F ≪≫
        (Scheme.Modules.restrictFunctorComp V.ι W.ι).app F ≪≫
        ((Scheme.Modules.overFunctorEquiv V).app
          ((Scheme.Modules.restrictFunctor W.ι).obj F)).symm) ≪≫
      ((Scheme.Modules.overEquiv V).unitIso.app
        (((Scheme.Modules.restrictFunctor W.ι).obj F).over V)).symm
  let eunit : SheafOfModules.unit (W.toScheme.ringCatSheaf.over V) ≅
      T.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (V.sheafOfModulesEquivOverInverseUnit W.toScheme.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv V).inverse.mapIso
        ((Scheme.Modules.restrictUnitIso s.hom).symm ≪≫
          (Scheme.Modules.restrictFunctor s.hom).mapIso
            (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      E.inverse.obj (SheafOfModules.unit (W.toScheme.ringCatSheaf.over V)) :=
    E.unitIso.app _ ≪≫ E.inverse.mapIso eunit.symm
  let e : E.inverse.obj (((Scheme.Modules.restrictFunctor W.ι).obj F).over V) ≅
      F.over U := E.inverse.mapIso eF.symm ≪≫ (E.unitIso.app _).symm
  let G' := (G.map E.inverse η).ofEpi e.hom
  exact ⟨G', inferInstance⟩

-- A cover of each member of an open cover refines to an open cover of the scheme.
private theorem imageCover (X : Scheme.{u}) (I : Type u)
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (J : I → Type u) (V : ∀ i, J i → (U i).toScheme.Opens)
    (hV : ∀ i, (_root_.Opens.grothendieckTopology (U i).toScheme).CoversTop (V i)) :
    (_root_.Opens.grothendieckTopology X).CoversTop
      (fun a : Σ i, J i ↦ (U a.1).ι ''ᵁ V a.1 a.2) := by
  intro W x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  have hc := (_root_.Opens.coversTop_iff (U i).toScheme (V i)).mp (hV i)
  have hxt : (⟨x, hi⟩ : U i) ∈ ⨆ j, V i j := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxt
  let Z := W ⊓ ((U i).ι ''ᵁ V i j)
  refine ⟨Z, homOfLE inf_le_left, ⟨⟨i, j⟩, ⟨homOfLE inf_le_right⟩⟩, ?_⟩
  exact ⟨hx, ⟨⟨x, hi⟩, hj, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Finite type is local for an open cover when each restricted module is coherent.
Source: Stacks Project, Definitions 01BV and 01B5 and Lemma 01B6.

Proof: Coherence gives finite local-generators data on every member of the cover.
For each generating neighbourhood, identify its scheme with the image open in `X`.
The open-site equivalences and restriction along that isomorphism identify the two
restricted modules and their structure modules. Transport the finite generating
family through this equivalence. Index the resulting neighbourhoods by the pairs
of a cover member and one of its generating neighbourhoods. Every point belongs
to one such image, so these opens cover `X`; the transported families are finite.
This is local-generators data witnessing finite type, including for the empty scheme.
(blueprint: lem-weil-pbc-coherent-module-finite-type-local-cover)
-/
theorem coherent_module_finite_type_local_cover
    (X : Scheme.{u}) (F : X.Modules) (I : Type u)
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hF : ∀ (i : I), RingedSpace.IsCoherent (U i).toScheme.toRingedSpace
      ((Scheme.Modules.restrictFunctor (U i).ι).obj F)) :
    F.IsFiniteType := by
  classical
  have ht (i : I) : ((Scheme.Modules.restrictFunctor (U i).ι).obj F).IsFiniteType :=
    (hF i).1
  have hd (i : I) :
      ∃ q : ((Scheme.Modules.restrictFunctor (U i).ι).obj F).LocalGeneratorsData,
        q.IsFiniteType := by
    have := ht i
    exact SheafOfModules.IsFiniteType.exists_localGeneratorsData _
  choose q hq using hd
  have hg (i : I) (j : (q i).I) :
      ∃ G : (F.over ((U i).ι ''ᵁ (q i).X j)).GeneratingSections, G.IsFiniteType := by
    have := (hq i).isFiniteType j
    exact transportGenerators X F (U i) ((q i).X j) ((q i).generators j)
  choose g hg using hg
  let d : F.LocalGeneratorsData :=
    { I := Σ i : I, (q i).I
      X a := (U a.1).ι ''ᵁ (q a.1).X a.2
      coversTop := imageCover X I U hU (fun i ↦ (q i).I) (fun i ↦ (q i).X)
        (fun i ↦ (q i).coversTop)
      generators a := g a.1 a.2 }
  have hd : d.IsFiniteType := by
    constructor
    intro a
    exact hg a.1 a.2
  apply SheafOfModules.IsFiniteType.mk (M := F)
  exact ⟨d, hd⟩

end AlgebraicGeometry
