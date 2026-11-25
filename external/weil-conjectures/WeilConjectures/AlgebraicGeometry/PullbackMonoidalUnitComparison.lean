/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Normalization of the monoidal pullback unit

Source: Stacks Project, Tags 01CD and 0096, canonical tensor pullback and its adjunction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The monoidal counit is the canonical pullback map of the structure sheaf.
Source: Stacks Project, Tag 01CD (Modules), and Tag 0096 (Sheaves).
(blueprint: lem-sc-pullback-monoidal-unit-comparison).

Proof: apply the pullback-pushforward adjunction's injective hom equivalence.
The image of pullbackObjUnitIso.hom is unitToPushforwardObjUnit, the structure-ring
map, by pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit. The monoidal
pullback is obtained by descending presheaf pullback followed by sheafification along
sheafification. Expand its unit with functorMonoidalOfComp_ε and invert the resulting
composite to compute its counit. The sheafification/pullback comparison is
leftAdjointUniq for the two composite adjunctions; its unit compatibility cancels the
comparison with the adjacent sheafification unit and counit. The remaining presheaf
pullback counit has adjoint the structure-ring map, by the defining presheaf monoidal
adjunction formula. Thus both images are unitToPushforwardObjUnit. Injectivity gives
the stated equality. This is a morphism equality, so works on empty schemes and for
arbitrary scheme morphisms; no closed-immersion or invertibility hypothesis is used. -/
theorem pullback_monoidal_unit_comparison {X Z : Scheme.{u}} (j : Z ⟶ X) :
    Functor.OplaxMonoidal.η (pullback j) = (pullbackObjUnitIso j).hom := by
  let : (sheafification X).Monoidal := sheafificationMonoidal X
  let : (sheafification Z).Monoidal := sheafificationMonoidal Z
  let G := _root_.PresheafOfModules.pullbackOfCommRingCat j.toRingCatPresheafHom ⋙
    sheafification Z
  let : G.Monoidal := presheafPullbackCompSheafificationMonoidal j
  let e := SheafOfModules.sheafificationCompPullback j.toRingCatSheafHom
  have hη : Functor.OplaxMonoidal.η (pullback j) =
      (pullback j).map (Functor.LaxMonoidal.ε (sheafification X)) ≫
        e.hom.app (MonoidalCategory.tensorUnit _) ≫ Functor.OplaxMonoidal.η G := by
    rfl
  have hunitX : Functor.OplaxMonoidal.η (sheafification X) =
      (sheafificationAdjunction X).counit.app (MonoidalCategory.tensorUnit X.Modules) := by
    rfl
  have hunitZ : Functor.OplaxMonoidal.η (sheafification Z) =
      (sheafificationAdjunction Z).counit.app (MonoidalCategory.tensorUnit Z.Modules) := by
    rfl
  have hGη : Functor.OplaxMonoidal.η G =
      (sheafification Z).map (Functor.OplaxMonoidal.η
        (_root_.PresheafOfModules.pullbackOfCommRingCat j.toRingCatPresheafHom)) ≫
          Functor.OplaxMonoidal.η (sheafification Z) := by rfl
  rw [hη]
  apply (cancel_epi ((pullback j).map (Functor.OplaxMonoidal.η (sheafification X)))).mp
  simp only [← Functor.map_comp_assoc, Functor.Monoidal.η_ε]
  let A := (sheafificationAdjunction X).comp (pullbackPushforwardAdjunction j)
  let B := (_root_.PresheafOfModules.adjunctionOfCommRingCat j.toRingCatPresheafHom).comp
    (sheafificationAdjunction Z)
  apply (A.homEquiv _ _).injective
  rw [hGη, hunitZ, hunitX]
  have he : e = A.leftAdjointUniq B := by rfl
  rw [he]
  erw [(pullback j).map_id, Category.id_comp]
  rw [A.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  erw [← B.homEquiv_unit]
  simp only [A, B, Adjunction.comp_homEquiv]
  rw [← (sheafificationAdjunction Z).homEquiv_counit]
  erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  erw [_root_.PresheafOfModules.adjunctionOfCommRingCat_homEquiv_η j.toRingCatPresheafHom]
  erw [(pullbackPushforwardAdjunction j).homEquiv_naturality_left]
  have hc : (pullbackPushforwardAdjunction j).homEquiv _ _
      (pullbackObjUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  erw [hc, (sheafificationAdjunction X).homEquiv_naturality_right,
    ← (sheafificationAdjunction X).homEquiv_symm_id,
    Equiv.apply_symm_apply, Category.id_comp]
  apply _root_.PresheafOfModules.hom_ext
  intro U
  ext
  change Functor.LaxMonoidal.ε
    (ModuleCat.restrictScalars (j.toRingCatPresheafHom.app U).hom) (1) = _
  rw [ModuleCat.restrictScalars_η]
  rfl

end AlgebraicGeometry.Scheme.Modules
