/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
/-! # The ordinary scalar pullback square on homotopy categories -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_algebraicGeometryIntegralResiduePullOrdinaryUnit
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
attribute [local irreducible] Mod.extendScalarsIsoComapInv
private theorem extendSquare_forget
    {C : Type*} [Category C] [MonoidalCategory C]
    [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]
    {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
    [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
    (a : R ⟶ R') [IsMonHom a] [IsIso a] (b : S ⟶ S') [IsMonHom b] [IsIso b]
    (sq : a ≫ ψ = φ ≫ b) (N : Mod C S) :
    ((Mod.extendScalarsComapIsoOfIsIso φ ψ a b sq).hom.app N).hom ≫
      ((Mod.extendScalarsIsoComapInv a).hom.app ((Mod.comap φ).obj N)).hom =
      ((Mod.extendScalarsIsoComapInv b).hom.app N).hom := by
  simp only [Mod.extendScalarsComapIsoOfIsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Mod.comp_hom', Mod.comap_map_hom,
    Mod.comapComp_hom_app_hom, Mod.comapComp_inv_app_hom,
    Mod.comapCongr_hom_app_hom]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.assoc,
    ← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom', Category.comp_id]

private theorem isoInvFac {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (u : Y ⟶ Z) (v : X ⟶ Z) (h : e.hom ≫ u = v) :
    e.inv ≫ v = u := by
  rw [← h, e.inv_hom_id_assoc]

private theorem unitCompositeMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : C ⥤ D} {S : D ⥤ C}
    {U : A ⥤ C} {T : C ⥤ A} {V : B ⥤ D} {W : D ⥤ B}
    (af : F ⊣ R) (ag : G ⊣ S) (au : U ⊣ T) (av : V ⊣ W)
    (e : W ⋙ R ≅ S ⋙ T) (q : R ⋙ U ⟶ V ⋙ S)
    (hq : ((mateEquiv av au).symm (TwoSquare.mk _ _ _ _ e.hom)) = q)
    (M : A) :
    U.map (af.unit.app M) ≫ q.app (F.obj M) =
      ag.unit.app (U.obj M) ≫ S.map
        ((Adjunction.pullIsoOfComapIso ag af au av e).hom.app M) := by
  have hi := iterated_mateEquiv_conjugateEquiv_symm af ag au av
    (TwoSquare.mk _ _ _ _ e.hom)
  have h := unit_mateEquiv_symm af ag (TwoSquare.mk _ _ _ _ q) M
  have hq' : (mateEquiv av au).symm (TwoSquare.mk _ _ _ _ e.hom) =
      TwoSquare.mk _ _ _ _ q := by
    ext
    exact congr_app hq _
  rw [hq'] at hi
  change U.map (af.unit.app M) ≫ q.app (F.obj M) = _ at h
  rw [hi] at h
  exact h

namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.comapUpperStarIso CondensedRing.comapLowerStarIso
  profinitePointModuleForgetPullbackIso
-- The concrete comparisons unfold several coefficient and module functor wrappers.
private theorem comapUpperStar_forget
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    ((CondensedRing.comapUpperStarIso a f).hom.app N).hom ≫
        (profinitePointModuleForgetPullbackIso Λ f).hom.app
          ((Mod.comap (coefficientMap a Y)).obj N) =
      (profinitePointModuleForgetPullbackIso Λ' f).hom.app N := by
  have hs := extendSquare_forget
    ((upperStar Ab.{u + 1} f).map (coefficientMap a Y))
    (coefficientMap a X) (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
    (map_coefficientMap_comp_condensedPullbackHom a f).symm
    (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ' Y)).obj N)
  let e := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)
  let z := ((upperStar Ab.{u + 1} f).mapModComapIso (coefficientMap a Y)).inv.app N
  have h := congrArg (fun k ↦ k.hom) (e.hom.naturality z)
  simp only [Mod.comp_hom', Mod.comap_map_hom] at h
  simp only [CondensedRing.comapUpperStarIso,
    profinitePointModuleForgetPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Mod.comp_hom', Mod.id_hom']
  erw [Category.id_comp, Category.comp_id]
  erw [Category.id_comp, Category.assoc, h]
  erw [← Category.assoc, hs]
  rfl

private theorem comapUpperStar_inv_forget_private
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    ((CondensedRing.comapUpperStarIso a f).inv.app N).hom ≫
        (profinitePointModuleForgetPullbackIso Λ' f).hom.app N =
      (profinitePointModuleForgetPullbackIso Λ f).hom.app
          ((Mod.comap (coefficientMap a Y)).obj N) := by
  let e := (Mod.forget (condensedRingObj Λ X)).mapIso
    ((CondensedRing.comapUpperStarIso a f).app N)
  exact isoInvFac e _ _ (comapUpperStar_forget a f N)

/-- Public export of the private `comapUpperStar_inv_forget_private`
(used by `import all` importers; linter.privateModule). -/
alias comapUpperStar_inv_forget := comapUpperStar_inv_forget_private

-- The concrete comparisons unfold several coefficient and module functor wrappers.
private theorem ordinary_vertical_unit
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    (Mod.comap (coefficientMap a Y)).map
        ((CondensedRing.upperStarLowerStarAdjunction Λ' f).unit.app N) ≫
      (CondensedRing.comapLowerStarIso a f).hom.app
        ((CondensedRing.upperStar Λ' f).obj N) =
    (CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app
        ((Mod.comap (coefficientMap a Y)).obj N) ≫
      (CondensedRing.lowerStar Λ f).map
        ((CondensedRing.comapUpperStarIso a f).inv.app N) := by
  apply Mod.hom_ext
  have : IsIso ((lowerStar Ab.{u + 1} f).map
      ((profinitePointModuleForgetPullbackIso Λ' f).hom.app N)) := inferInstance
  apply (cancel_mono ((lowerStar Ab.{u + 1} f).map
      ((profinitePointModuleForgetPullbackIso Λ' f).hom.app N))).1
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    CondensedRing.comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
    Category.assoc]
  erw [Category.id_comp]
  have hm : ((CondensedRing.lowerStar Λ f).map
      ((CondensedRing.comapUpperStarIso a f).inv.app N)).hom ≫
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ' f).hom.app N) =
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).hom.app
          ((Mod.comap (coefficientMap a Y)).obj N)) := by
    change (lowerStar Ab.{u + 1} f).map
      (((CondensedRing.comapUpperStarIso a f).inv.app N).hom) ≫ _ = _
    erw [← Functor.map_comp, comapUpperStar_inv_forget_private]
  erw [hm, moduleUnit_forget Λ' f N,
    moduleUnit_forget Λ f ((Mod.comap (coefficientMap a Y)).obj N)]
  rfl

-- The concrete comparisons unfold several coefficient and module functor wrappers.
private theorem ordinaryScalarUnit_private
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (CondensedRing.upperStar Λ f).map
        ((Mod.extendRestrictAdjunction (coefficientMap a Y)).unit.app M) ≫
      (CondensedRing.comapUpperStarIso a f).inv.app
        ((Mod.extendScalars (coefficientMap a Y)).obj M) =
    (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app
        ((CondensedRing.upperStar Λ f).obj M) ≫
      (Mod.comap (coefficientMap a X)).map ((CondensedRing.pullIso a f).hom.app M) := by
  let au := CondensedRing.upperStarLowerStarAdjunction Λ f
  let av := CondensedRing.upperStarLowerStarAdjunction Λ' f
  let e := CondensedRing.comapLowerStarIso a f
  have hq : ((mateEquiv av au).symm (TwoSquare.mk _ _ _ _ e.hom)) =
      (CondensedRing.comapUpperStarIso a f).inv := by
    apply NatTrans.ext
    funext N
    apply (au.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm av au (TwoSquare.mk _ _ _ _ e.hom) N).symm.trans
      (ordinary_vertical_unit a f N)
  exact unitCompositeMate (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (Mod.extendRestrictAdjunction (coefficientMap a X)) au av e
    (CondensedRing.comapUpperStarIso a f).inv hq M

/-- Public export of the private `ordinaryScalarUnit_private`
(used by `import all` importers; linter.privateModule). -/
alias ordinaryScalarUnit := ordinaryScalarUnit_private
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
end AlgebraicGeometry.ProEtale.CondensedRing
