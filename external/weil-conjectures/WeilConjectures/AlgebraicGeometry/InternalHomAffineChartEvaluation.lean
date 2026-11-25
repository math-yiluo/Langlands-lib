/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine chart equivalences for internal Hom

Source: Stacks Project, schemes.tex, Tag 01I7; duality.tex, Tag 0BUZ.
(blueprint: lem-sc-internal-hom-affine-chart-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of the affine chart, with their original scalar action. 
(blueprint: lem-sc-internal-hom-affine-chart-evaluation)
-/
noncomputable def chartSectionsEquiv {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  have htop : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let e : Γ(M.restrict hU.fromSpec, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso hU.fromSpec ⊤ ≪≫ M.presheaf.mapIso (eqToIso htop.symm).op
  refine { e.addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r x
  change M.presheaf.map (eqToHom htop.symm).op
      ((M.restrictAppIso hU.fromSpec ⊤).hom (r • x)) = _
  rw [Scheme.Modules.restrictAppIso_fromSpec_smul, Scheme.Modules.map_smul,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  have hid : (homOfLE (hU.fromSpec_image_le ⊤)).op ≫ (eqToHom htop.symm).op = 𝟙 (op U) :=
    Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rfl

open Scheme.Modules
set_option backward.isDefEq.respectTransparency false in
/-- Restriction along an isomorphism is an equivalence. 
(blueprint: lem-sc-internal-hom-affine-chart-evaluation)
-/
noncomputable def isoRestrictEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Y.Modules ≌ X.Modules := by
  let F := restrictFunctor f
  let G := restrictFunctor (inv f)
  have η : 𝟭 Y.Modules ≅ F ⋙ G :=
    restrictFunctorId.symm ≪≫
      (restrictFunctorCongr (IsIso.inv_hom_id f).symm) ≪≫ restrictFunctorComp (inv f) f
  have ε : G ⋙ F ≅ 𝟭 X.Modules :=
    (restrictFunctorComp f (inv f)).symm ≪≫
      restrictFunctorCongr (IsIso.hom_inv_id f) ≪≫ restrictFunctorId
  have : F.IsEquivalence := Functor.IsEquivalence.mk' G η ε
  exact F.asEquivalence
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms on the over-site identified with morphisms on the affine chart. 
(blueprint: lem-sc-internal-hom-affine-chart-evaluation)
-/
noncomputable def chartHomEquiv {X : Scheme.{u}} (M F : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    (SheafOfModules.homObj M F).val.obj (op U) ≃
      (M.restrict hU.fromSpec ⟶ F.restrict hU.fromSpec) := by
  let e₀ := ((SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).homEquiv
    (X := M.over U) (Y := F.over U)).symm
  let e₁ := (overEquiv U).fullyFaithfulFunctor.homEquiv
    (X := M.over U) (Y := F.over U)
  let e₂ := Iso.homCongr ((overFunctorEquiv U).app M) ((overFunctorEquiv U).app F)
  let e₃ := (isoRestrictEquiv hU.isoSpec.inv).fullyFaithfulFunctor.homEquiv
    (X := M.restrict U.ι) (Y := F.restrict U.ι)
  let e₄ := Iso.homCongr ((restrictFunctorComp hU.isoSpec.inv U.ι).app M).symm
    ((restrictFunctorComp hU.isoSpec.inv U.ι).app F).symm
  exact e₀.trans (e₁.trans (e₂.trans (e₃.trans e₄)))

set_option backward.isDefEq.respectTransparency false in
/-- The constructed chart equivalences preserve evaluation at the terminal open.

Source: Stacks Project, schemes.tex, Tag 01I7; duality.tex, Tag 0BUZ.
(blueprint: lem-sc-internal-hom-affine-chart-evaluation).

Proof: The fully faithful forgetful functor identifies a presheaf morphism over U with
its sheaf morphism, keeping each component. The over-site equivalence is induced by
Opens.overEquivalence; its functor evaluates at the image open and transports scalars
by the structure-sheaf comparison. The natural isomorphism overFunctorEquiv identifies
this with restriction along U.ι. Restriction along hU.isoSpec.inv again keeps the
component at its image open. The restrictFunctorComp isomorphisms transport these
components through the equality of composite image opens. On the terminal open the
composite image is U. The section equivalences on source and target are precisely
restrictAppIso followed by transport along fromSpec '' ⊤ = U. Conjugating therefore
cancels those transports and gives the original component at Over.mk (𝟙 U).
This argument uses no quasi-coherence; it also applies to empty opens. -/
theorem internalHom_evaluation_chart_compare {X : Scheme.{u}} (M F : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U)
    (φ : (SheafOfModules.homObj M F).val.obj (op U)) :
    (LinearEquiv.arrowCongr (chartSectionsEquiv M U hU) (chartSectionsEquiv F U hU))
      ((moduleSpecΓFunctor (R := Γ(X, U))).map (chartHomEquiv M F U hU φ)).hom =
        (φ.app (op (Over.mk (𝟙 U)))).hom := by
  let ψ : M.over U ⟶ F.over U :=
    (SheafOfModules.fullyFaithfulForget _).preimage φ
  let V : TopologicalSpace.Opens U := hU.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)
  ext s
  simp only [LinearEquiv.arrowCongr_apply]
  dsimp [chartSectionsEquiv, chartHomEquiv, Iso.homCongr, isoRestrictEquiv,
    Functor.asEquivalence, Functor.FullyFaithful.homEquiv]
  change F.presheaf.map _
    (((restrictFunctorComp hU.isoSpec.inv U.ι).inv.app F).app ⊤
      (((overFunctorEquiv U).hom.app F).app V
        (((overEquiv U).functor.map ψ).app V
          (((overFunctorEquiv U).inv.app M).app V
            (((restrictFunctorComp hU.isoSpec.inv U.ι).hom.app M).app ⊤
              (M.presheaf.map _ s)))))) = _
  simp only [restrictFunctorComp_inv_app_app, restrictFunctorComp_hom_app_app]
  have hhom (N : X.Modules) (W : (U : Scheme).Opens)
      (x : Γ((overEquiv U).functor.obj (N.over U), W)) :
      ((overFunctorEquiv U).hom.app N).app W x = x := rfl
  have hinv (N : X.Modules) (W : (U : Scheme).Opens)
      (x : Γ(N.restrict U.ι, W)) :
      ((overFunctorEquiv U).inv.app N).app W x = x := rfl
  simp only [hhom, hinv]
  change F.presheaf.map _ (F.presheaf.map _
    (φ.app (op ((TopologicalSpace.Opens.overEquivalence U).inverse.obj V))
      (M.presheaf.map _ (M.presheaf.map _ s)))) = _
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  let W := (TopologicalSpace.Opens.overEquivalence U).inverse.obj V
  change F.presheaf.map _ (φ.app (op W) (M.presheaf.map W.hom.op s)) = _
  have hn := PresheafOfModules.naturality_apply φ
    (Over.homMk W.hom : W ⟶ Over.mk (𝟙 U)).op s
  change φ.app (op W) (M.presheaf.map W.hom.op s) =
    F.presheaf.map W.hom.op (φ.app (op (Over.mk (𝟙 U))) s) at hn
  rw [hn]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change F.presheaf.map (𝟙 (op U)) (φ.app (op (Over.mk (𝟙 U))) s) = _
  erw [CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry
