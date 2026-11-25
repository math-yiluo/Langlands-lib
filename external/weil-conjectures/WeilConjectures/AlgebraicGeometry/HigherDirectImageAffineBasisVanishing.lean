/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
import WeilConjectures.Topology.RestrictInjectiveResolution
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Vanishing of higher direct image on an affine neighbourhood basis

Source: Stacks Project, Tags 01E4 and 01E1.
(blueprint: lem-pc-higher-direct-image-affine-basis-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Open restriction preserves limits, since its underlying abelian presheaf is
precomposition by the open-image functor. -/
private theorem affine_basis_restrict_preservesLimits {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesLimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) := by
  have : PreservesLimitsOfSize.{u, u}
      ((Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ AddCommGrpCat.{u}).obj
        j.opensFunctor.op) :=
    preservesLimits_of_evaluation _ fun U ↦ inferInstanceAs
      (PreservesLimitsOfSize.{u, u}
        ((evaluation _ _).obj (j.opensFunctor.op.obj U)))
  have : PreservesLimitsOfSize.{u, u}
      (Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf X) :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u}
      (Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ _).obj j.opensFunctor.op))
  have : ReflectsLimitsOfSize.{u, u} (Scheme.Modules.toPresheaf X) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves
    (Scheme.Modules.restrictFunctor j) (Scheme.Modules.toPresheaf X)

set_option backward.isDefEq.respectTransparency.types true in
private noncomputable def affine_basis_pushforward_restrict_square
    {X T T' X' : Scheme.{u}} (f : X ⟶ T)
    (g : T' ⟶ T) [IsOpenImmersion g] (g' : X' ⟶ X) [IsOpenImmersion g']
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor g' ⋙ Scheme.Modules.pushforward f' := by
  unfold Scheme.Modules.restrictFunctor Scheme.Modules.pushforward
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  let e : g.opensFunctor ⋙ TopologicalSpace.Opens.map f.base ≅
      TopologicalSpace.Opens.map f'.base ⋙ g'.opensFunctor :=
    NatIso.ofComponents (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W).symm)
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  ext W x
  change X.presheaf.map
      (eqToHom (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        sq.flip W.unop)).op
      (f.app (g ''ᵁ W.unop) ((g.appIso W.unop).inv x)) =
    (g'.appIso (f' ⁻¹ᵁ W.unop)).inv (f'.app W.unop x)
  have h : f.app (g ''ᵁ W.unop) ≫
      X.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
          sq.flip W.unop)).op ≫ (g'.appIso (f' ⁻¹ᵁ W.unop)).hom =
      (g.appIso W.unop).hom ≫ f'.app W.unop := by
    simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact sq.w
  have hx := ConcreteCategory.congr_hom h ((g.appIso W.unop).inv x)
  apply (ConcreteCategory.bijective_of_isIso (g'.appIso (f' ⁻¹ᵁ W.unop)).hom).1
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply,
    Iso.hom_inv_id_apply] using hx


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing of cohomology on inverse images of affine opens of U implies vanishing
of the p-th higher direct image restricted to U. No quasi-coherence is required.
Source: Stacks Project, Tag 01E4 (sheafified cohomology presheaf) and Tag 01E1
(restriction of injective resolutions).
(blueprint: lem-pc-higher-direct-image-affine-basis-vanishing).

Proof: Restrict an injective resolution of F to f^{-1}U. It remains injective and
computes the open cohomology of the restricted coefficient module. Higher direct
image commutes with open restriction, by this same restricted resolution. Tag 01E4
identifies it with the sheafification of the presheaf V maps to H^p(g^{-1}V,F|_Y),
where Y=f^{-1}U and g=f|_U. Every point of U has an affine neighbourhood basis and
all these presheaf values are zero by the hypothesis. Its stalks, the filtered
colimits of these values, are zero; sheafification preserves stalks. Thus every
stalk of the restricted higher direct image is zero, and the module sheaf is zero.
This includes degree zero, empty U, and empty inverse images. -/
theorem isZero_restrict_higherDirectImage_of_affine_basis
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (F : X.Modules) (p : ℕ)
    (h : ∀ (V : U.toScheme.Opens), IsAffineOpen V →
      IsZero ((RingedSpace.openModuleCohomology (f ⁻¹ᵁ U).toScheme.toRingedSpace p
        ((f ∣_ U) ⁻¹ᵁ V)).obj (Scheme.Modules.restrict F (f ⁻¹ᵁ U).ι))) :
    IsZero (Scheme.Modules.restrict
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F) U.ι) := by
  let Y := (f ⁻¹ᵁ U).toScheme
  let T := U.toScheme
  let g : Y ⟶ T := f ∣_ U
  let G : Y.Modules := Scheme.Modules.restrict F (f ⁻¹ᵁ U).ι
  let : EnoughInjectives Y.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
  let : (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).Additive :=
    RingedSpace.moduleDirectImage_additive g.toLRSHom.toShHom
  let I := injectiveResolution G
  let K : CochainComplex T.Modules ℕ :=
    ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex
  let P := Scheme.Modules.sectionCohomologyPresheaf K p
  have hP (V : T.Opens) (hV : IsAffineOpen V) :
      IsZero (P.presheaf.obj (Opposite.op V)) := by
    let L := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K
    let E := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
      (evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)
    let : (RingedSpace.openModuleSections Y.toRingedSpace (g ⁻¹ᵁ V)).Additive :=
      RingedSpace.openModuleSections_additive _ _
    let e := I.isoRightDerivedObj
      (RingedSpace.openModuleSections Y.toRingedSpace (g ⁻¹ᵁ V)) p
    exact (h V hV).of_iso
      (((L.sc p).mapHomologyIso E).symm ≪≫ e.symm)
  have hstalk (x : T) :
      IsZero ((PresheafOfModules.moduleStalkFunctor T.ringCatSheaf.obj x).obj P) := by
    suffices hs : Subsingleton
        ((PresheafOfModules.moduleStalkFunctor T.ringCatSheaf.obj x).obj P) from
      @ModuleCat.isZero_of_subsingleton _ _ _ hs
    refine ⟨fun a b ↦ ?_⟩
    have hz (a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (X := T.toTopCat) P.presheaf x) : a = 0 := by
      obtain ⟨V, hxV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := T.toTopCat) P.presheaf a
      obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
      have : Subsingleton (P.presheaf.obj (Opposite.op W)) :=
        AddCommGrpCat.subsingleton_of_isZero (hP W hW)
      rw [← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE hWV) x hxW a]
      have ha : P.presheaf.map (homOfLE hWV).op a = 0 := Subsingleton.elim _ _
      exact (congrArg (TopCat.Presheaf.germ P.presheaf W x hxW) ha).trans (map_zero _)
    exact (hz a).trans (hz b).symm
  have hD : IsZero
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived p).obj G) := by
    let D := ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived p).obj G
    let A := SheafOfModules.toSheaf T.ringCatSheaf
    suffices hA : IsZero (A.obj D) from
      (IsZero.iff_id_eq_zero D).mpr (A.map_injective (hA.eq_of_src _ _))
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (A.obj D)).mpr
    intro x
    have hi := (higherDirectImagePresheaf g G I p).2.2.1 x
    let τ := (PresheafOfModules.moduleStalkFunctor T.ringCatSheaf.obj x).map
      (Scheme.Modules.sectionCohomologyTheta K p ≫
        (SheafOfModules.forget T.ringCatSheaf).map
          (I.isoRightDerivedObj (RingedSpace.moduleDirectImage g.toLRSHom.toShHom) p).inv)
    have : IsIso τ := hi
    have hs := ModuleCat.subsingleton_of_isZero ((hstalk x).of_iso (asIso τ).symm)
    exact @AddCommGrpCat.isZero_of_subsingleton _ hs
  let A := Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let B := Scheme.Modules.restrictFunctor U.ι
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : PreservesLimitsOfSize.{u, u} A :=
    affine_basis_restrict_preservesLimits (f ⁻¹ᵁ U).ι
  let : PreservesLimitsOfSize.{u, u} B := affine_basis_restrict_preservesLimits U.ι
  let : A.Additive := by
    constructor
    intro M N φ ψ
    rfl
  let : B.Additive := by
    constructor
    intro M N φ ψ
    rfl
  let I₀ := injectiveResolution F
  have hinj (n : ℕ) : Injective (A.obj (I₀.cocomplex.X n)) := by
    have hi := (RingedSpace.restrict_injectiveResolution X.toRingedSpace (f ⁻¹ᵁ U)
      F I₀).2 n
    have hj := (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).functor.injective_obj
      ((SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).obj (I₀.cocomplex.X n))
    exact Injective.of_iso
      ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app (I₀.cocomplex.X n)) hj
  let J : InjectiveResolution (A.obj F) :=
    { cocomplex := (A.mapHomologicalComplex (.up ℕ)).obj I₀.cocomplex
      injective := hinj
      ι := (HomologicalComplex.singleMapHomologicalComplex A (.up ℕ) 0).inv.app F ≫
        (A.mapHomologicalComplex (.up ℕ)).map I₀.ι }
  let e := affine_basis_pushforward_restrict_square f U.ι (f ⁻¹ᵁ U).ι g
    (isPullback_morphismRestrict f U).flip
  let K₀ := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj I₀.cocomplex
  let eK := (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I₀.cocomplex ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ Scheme.Modules.pushforward g))
      (.up ℕ)).symm.app I₀.cocomplex
  let c := J.isoRightDerivedObj (Scheme.Modules.pushforward g) p ≪≫
    (HomologicalComplex.homologyFunctor T.Modules (.up ℕ) p).mapIso eK.symm ≪≫
    (K₀.sc p).mapHomologyIso B ≪≫
    B.mapIso (I₀.isoRightDerivedObj (Scheme.Modules.pushforward f) p).symm
  exact hD.of_iso c.symm

end AlgebraicGeometry
