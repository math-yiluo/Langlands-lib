import Langlands.AlgebraicGeometry.Modules.RelativeFlatness

/-! # Linear restriction-stalk comparisons -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

private lemma stalkMap_germ_appIso_inv (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) :
    f.stalkMap x (Y.presheaf.germ (f ''ᵁ U) (f x) (by simpa) ((f.appIso U).inv r)) =
      X.presheaf.germ U x hx r := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ (f ⁻¹ᵁ f ''ᵁ U) x _
      (((f.appIso U).inv ≫ f.app (f ''ᵁ U)) r) = _
  rw [Scheme.Hom.appIso_inv_app]
  exact X.presheaf.germ_res_apply (eqToHom (f.preimage_image_eq U)) x (by simpa) r

private lemma restrictStalk_germ (M : Y.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U) (m : Γ(M.restrict f, U)) :
    ((Scheme.Modules.restrictStalkNatIso f x).hom.app M)
        ((M.restrict f).presheaf.germ U x hx m) =
      M.presheaf.germ (f ''ᵁ U) (f x) (by simpa) m :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x M hx) m

private lemma restrictStalk_map_smul (M : Y.Modules) (x : X)
    (r : Y.presheaf.stalk (f x)) (m : stalk (M.restrict f) x) :
    ((Scheme.Modules.restrictStalkNatIso f x).hom.app M)
        ((f.stalkMap x) r • m) =
      @SMul.smul (Y.presheaf.stalk (f x)) (stalk M (f x)) _
        r (((Scheme.Modules.restrictStalkNatIso f x).hom.app M) m) := by
  obtain ⟨U, hxU, a, ha⟩ := X.presheaf.exists_germ_eq ((f.stalkMap x) r)
  obtain ⟨V, hVU, hxV, m, rfl⟩ := (M.restrict f).presheaf.exists_le_germ_eq m hxU
  let b : Γ(X, V) := X.presheaf.map (homOfLE hVU).op a
  have hb : X.presheaf.germ V x hxV b = (f.stalkMap x) r := by
    rw [X.presheaf.germ_res_apply]
    exact ha
  have hr : Y.presheaf.germ (f ''ᵁ V) (f x) (by simpa) ((f.appIso V).inv b) = r := by
    apply (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).injective
    rw [stalkMap_germ_appIso_inv f x V hxV, hb]
  rw [← hb]
  erw [← PresheafOfModules.germ_smul (M.restrict f).val x V hxV]
  erw [restrictStalk_germ, restrictStalk_germ]
  rw [← hr]
  exact PresheafOfModules.germ_smul M.val (f x) (f ''ᵁ V) (by simpa) _ _

/-- Restriction along an open immersion preserves the actual module stalk,
linearly over the original local ring. The restricted stalk carries the
scalar action through the actual map of local rings. -/
def restrictStalkLinearEquiv (M : Y.Modules) (x : X) :
    letI := relativeStalkModule f (M.restrict f) x
    stalk (M.restrict f) x ≃ₗ[Y.presheaf.stalk (f x)] stalk M (f x) := by
  letI := relativeStalkModule f (M.restrict f) x
  exact {
    __ := ((Scheme.Modules.restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv
    map_smul' := restrictStalk_map_smul f M x }

@[simp]
lemma restrictStalkLinearEquiv_germ (M : Y.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U) (m : Γ(M.restrict f, U)) :
    restrictStalkLinearEquiv f M x ((M.restrict f).presheaf.germ U x hx m) =
      M.presheaf.germ (f ''ᵁ U) (f x) (by simpa) m :=
  restrictStalk_germ f M x U hx m

/-- Transport a rank-one local-ring basis to the stalk on an open restriction. -/
def restrictStalkRankOneEquiv (M : Y.Modules) (x : X)
    (e : stalk M (f x) ≃ₗ[Y.presheaf.stalk (f x)] Y.presheaf.stalk (f x)) :
    stalk (M.restrict f) x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let eR := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  let eS := ((Scheme.Modules.restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv
  refine {
    __ := (eS.trans e.toAddEquiv).trans eR.toAddEquiv
    map_smul' := ?_ }
  intro a m
  obtain ⟨r, rfl⟩ := eR.surjective a
  change eR (e (eS ((f.stalkMap x) r • m))) = eR r * eR (e (eS m))
  erw [restrictStalk_map_smul f M x, e.map_smul]
  exact eR.map_mul _ _

/-- A rank-one basis on an open restriction gives a rank-one basis of the
original stalk over its original local ring. -/
def ofRestrictStalkRankOneEquiv (M : Y.Modules) (x : X)
    (e : stalk (M.restrict f) x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) :
    stalk M (f x) ≃ₗ[Y.presheaf.stalk (f x)] Y.presheaf.stalk (f x) := by
  letI := relativeStalkModule f (M.restrict f) x
  let eR := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  let eS := (restrictStalkLinearEquiv f M x).symm
  refine {
    __ := (eS.toAddEquiv.trans e.toAddEquiv).trans eR.symm.toAddEquiv
    map_smul' := ?_ }
  intro r m
  change eR.symm (e (eS (r • m))) = r * eR.symm (e (eS m))
  rw [eS.map_smul]
  change eR.symm (e ((f.stalkMap x) r • eS m)) = _
  rw [e.map_smul]
  change eR.symm (eR r * e (eS m)) = _
  rw [map_mul, eR.symm_apply_apply]

end Langlands.AlgebraicGeometry.Modules
