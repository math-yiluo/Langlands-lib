/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.CategoryTheory.Sites.SheafPullbackModuleFlat

/-!
# Flat module objects under pullback from the condensed point

Let `Λ` be a commutative condensed ring and `X` a scheme. The pullback
`p_X^* : Mod_Λ ⥤ Mod_{Λ_X}` of module objects from the condensed point preserves flat objects
(`AlgebraicGeometry.ProEtale.preservesFlat_mapMod_upperStarFromPoint`).

Writing `p_X^* = π_X^* ∘ p^*` with `π_X : X ⟶ Spec ℤ`, both factors are inverse images of
ringed sites along continuous, representably flat functors of sites, and these preserve flat
modules (Stacks Project, Tag 05VD).

Source: Stacks Project, Tag 05VD; HRS Section 3 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback of module objects from the condensed point to `(Spec ℤ)_proét` preserves flat
objects. Source: Stacks Project, Tag 05VD (auxiliary; not a blueprint node). -/
theorem preservesFlat_mapMod_pointUpperStar : (pointUpperStar.{u}.mapMod Λ).PreservesFlat := by
  have h := Functor.sheafPullbackConstruction.preservesFlat_mapModComap
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ.{u}) profiniteToProEt Λ
    (pointUpperStar.{u}.obj Λ) (𝟙 _)
  let e : Mod.mapModComap (𝟙 (pointUpperStar.{u}.obj Λ)) ≅ pointUpperStar.{u}.mapMod Λ :=
    Functor.isoWhiskerLeft _ (Mod.comapId _) ≪≫ Functor.rightUnitor _
  exact ⟨fun hM ↦ ObjectProperty.prop_of_iso _ (e.app _) (h.flat_obj hM)⟩

/-- The pullback `p_X^* : Mod_Λ ⥤ Mod_{Λ_X}` of module objects from the condensed point
preserves flat objects.

Source: Stacks Project, Tag 05VD (auxiliary; not a blueprint node).

Proof: `p_X^*` is the composite of `p^*` and `π_X^*`. On module objects this composite is
`p^*` followed by `π_X^*` and the restriction of scalars along the identity comparison of
coefficient rings; the first factor preserves flat objects by
`preservesFlat_mapMod_pointUpperStar`, the second by `inverseImageModule_preservesFlat`. -/
theorem preservesFlat_mapMod_upperStarFromPoint (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).PreservesFlat := by
  let F := pointUpperStar.{u}
  let G := (toSpecZ X)^*[Ab.{u + 1}]
  let τ : F ⋙ G ⟶ upperStarFromPoint X := 𝟙 (upperStarFromPoint X)
  have : NatTrans.IsMonoidal τ := inferInstanceAs (NatTrans.IsMonoidal (𝟙 (F ⋙ G)))
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (F ⋙ G)))
  let α := Functor.compAlgHom F G τ Λ
  have h₁ : (F.mapMod Λ).PreservesFlat := preservesFlat_mapMod_pointUpperStar Λ
  have h₂ : (Mod.mapModComap (inv α)).PreservesFlat :=
    inverseImageModule_preservesFlat (toSpecZ X) (F.obj Λ) ((upperStarFromPoint X).obj Λ) (inv α)
  let e : F.mapMod Λ ⋙ Mod.mapModComap (inv α) ≅ (upperStarFromPoint X).mapMod Λ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapModCompIso F G τ Λ) (Mod.comap (inv α)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Mod.comapComp (inv α) α).symm ≪≫
        Mod.comapCongr (IsIso.inv_hom_id α) ≪≫ Mod.comapId _) ≪≫
      Functor.rightUnitor _
  exact ⟨fun hM ↦ ObjectProperty.prop_of_iso _ (e.app _) (h₂.flat_obj (h₁.flat_obj hM))⟩

end AlgebraicGeometry.ProEtale
