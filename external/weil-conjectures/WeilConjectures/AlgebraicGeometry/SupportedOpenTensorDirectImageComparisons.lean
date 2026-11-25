/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Supported-open comparisons before the projection formula

Source: Stacks Project, Tags 08EV, 08DF, 08DX and 08DW.
(blueprint: lem-pc-supported-open-tensor-direct-image-comparisons).
-/

@[expose] public section

universe u w wO

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem supportedTensor_zero_of_homology_zero {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (E : DerivedCategory C)
    (h : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj E)) :
    IsZero E := by
  have hi : IsIso (0 : E ⟶ 0) := (DerivedCategory.isIso_iff C _).mpr (fun n ↦
    IsZero.isIso (h n) ((DerivedCategory.homologyFunctor C n).map_isZero
      (isZero_zero _)) _)
  exact (isZero_zero _).of_iso (asIso (0 : E ⟶ 0))

/-- Exact open restriction detects stalkwise vanishing, in any localization universe. -/
private theorem supportedTensor_restriction_zero (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hE : ∀ (n : ℤ) (x : X), x ∈ U → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf x))) :
    IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj E) := by
  apply supportedTensor_zero_of_homology_zero
  intro n
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E
  have hz : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).obj M) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    ext V z
    change z = 0
    apply TopCat.Presheaf.section_ext
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M)
    intro x hx
    change TopCat.Presheaf.germ M.val.presheaf _ x hx _ =
      TopCat.Presheaf.germ M.val.presheaf _ x hx _
    exact (hE n x (leOfHom V.unop.hom hx)).elim _ _
  let e := Scheme.Modules.overEquiv U
  exact (e.functor.map_isZero hz).of_iso
    (((schemeOpenRestriction X U).mapDerivedCategoryHomologyFunctorIso n).symm.app E)

private noncomputable def supportedTensor_restriction_stalk_iso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (n : ℤ) (x : U.toScheme) :
    TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor _ n).obj
      ((schemeOpenRestriction X U).mapDerivedCategory.obj E)).val.presheaf x ≅
    TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf x.val := by
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E
  exact H.mapIso (((schemeOpenRestriction X U).mapDerivedCategoryHomologyFunctorIso n).symm.app E)
    ≪≫ H.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
    ≪≫ (Scheme.Modules.restrictStalkNatIso U.ι x).app M

private theorem supportedTensor_stalk_zero_of_restriction_zero
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hE : IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj E))
    (n : ℤ) (x : U.toScheme) :
    Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf x.val)) := by
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  have : (Scheme.Modules.toPresheaf U.toScheme).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hz := H.map_isZero ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).map_isZero hE)
  let i := supportedTensor_restriction_stalk_iso X U E n x
  exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp
    (AddCommGrpCat.isZero_iff_subsingleton.mp hz)

/-- Closed support is preserved by derived direct image; use standard auxiliary opens. -/
private theorem supportedTensor_direct_image_support {Y X : Scheme.{u}} (f : Y ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) (hT : IsClosed T) (E : schemeDerivedCategory Y)
    (hE : ∀ (n : ℤ) (y : Y), f y ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf y))) :
    ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj
        ((schemeDerivedDirectImage f).obj E)).val.presheaf x)) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let U := f ⁻¹ᵁ V
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  have hz := supportedTensor_restriction_zero Y U E hE
  obtain ⟨bc⟩ := schemeDerivedDirectImage_openRestriction f V
  have hout : IsZero ((schemeOpenRestriction X V).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj E)) :=
    ((schemeDerivedDirectImage (f ∣_ V)).map_isZero hz).of_iso (bc.app E)
  intro n x hx
  exact supportedTensor_stalk_zero_of_restriction_zero X V _ hout n ⟨x, hx⟩

private theorem supportedTensor_tensor_support (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E F : schemeDerivedCategory X)
    (hE : ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf x))) :
    ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj (E ⊗ F)).val.presheaf x)) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let R := (schemeOpenRestriction X V).mapDerivedCategory
  have hz := supportedTensor_restriction_zero X V E hE
  obtain ⟨e⟩ := derivedTensor_openRestriction_iso_universes X V E F
  have : PreservesColimitsOfShape (Discrete PEmpty.{u + 1}) (tensorRight (R.obj F)) :=
    derivedTensorRight_preservesCoproducts V.toScheme (R.obj F) PEmpty.{u + 1}
  have : PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight (R.obj F)) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.equivPEmpty PEmpty.{u + 1})) _
  have hout : IsZero (R.obj (E ⊗ F)) :=
    ((tensorRight (R.obj F)).map_isZero hz).of_iso e
  intro n x hx
  exact supportedTensor_stalk_zero_of_restriction_zero X V _ hout n ⟨x, hx⟩

private theorem supportedTensor_restriction_detects_iso (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    {E F : schemeDerivedCategory X} (a : E ⟶ F)
    (hU : IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map a))
    (hV : IsIso ((schemeOpenRestriction X V).mapDerivedCategory.map a)) : IsIso a := by
  apply (DerivedCategory.isIso_iff _ a).2
  intro n
  let W : Bool → X.Opens := fun b ↦ if b then U else V
  have hW : ⨆ b, W b = ⊤ := by simpa [W, iSup_bool_eq] using hcover
  apply (sheaf_module_isIso_iff_isIso_over_open_cover
    X.toRingedSpace Bool W hW _ _ _).2
  intro b
  have hu : IsIso ((schemeOpenRestriction X U).map
      ((DerivedCategory.homologyFunctor _ n).map a)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction X U).mapDerivedCategoryHomologyFunctorIso n) a).mpr
        (by dsimp; infer_instance)
  have hv : IsIso ((schemeOpenRestriction X V).map
      ((DerivedCategory.homologyFunctor _ n).map a)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction X V).mapDerivedCategoryHomologyFunctorIso n) a).mpr
        (by dsimp; infer_instance)
  cases b
  · change IsIso ((SheafOfModules.overFunctor _ V).map
      ((DerivedCategory.homologyFunctor _ n).map a))
    change IsIso ((Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctor _ V).map
        ((DerivedCategory.homologyFunctor _ n).map a))) at hv
    let := hv
    exact isIso_of_reflects_iso _ (Scheme.Modules.overEquiv V).functor
  · change IsIso ((SheafOfModules.overFunctor _ U).map
      ((DerivedCategory.homologyFunctor _ n).map a))
    change IsIso ((Scheme.Modules.overEquiv U).functor.map
      ((SheafOfModules.overFunctor _ U).map
        ((DerivedCategory.homologyFunctor _ n).map a))) at hu
    let := hu
    exact isIso_of_reflects_iso _ (Scheme.Modules.overEquiv U).functor

private theorem supportedTensor_supported_unit_iso (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (E : schemeDerivedCategory X)
    (hE : ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj E).val.presheaf x))) :
    IsIso (adj.unit.app E) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  have hcover : U ⊔ V = ⊤ := by
    ext x
    change (x ∈ U ∨ x ∉ T) ↔ x ∈ (Set.univ : Set X)
    simp only [Set.mem_univ, iff_true]
    by_cases hx : x ∈ T
    · exact Or.inl (hTU hx)
    · exact Or.inr hx
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : schemeOpenRestriction X U ⊣ G :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  have : G.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : G.Full := (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : G.Faithful :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  have hi : IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map (adj.unit.app E)) :=
    isIso_of_comp_hom_eq_id _ (adj.left_triangle_components E)
  have hs : ∀ (n : ℤ) (x : U.toScheme), U.ι x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor _ n).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E)).val.presheaf x)) := by
    intro n x hx
    let i := supportedTensor_restriction_stalk_iso X U E n x
    exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
      (hE n x.val hx)
  have hr := supportedTensor_direct_image_support U.ι T hT _ hs
  exact supportedTensor_restriction_detects_iso X U V hcover (adj.unit.app E) hi
    (IsZero.isIso (supportedTensor_restriction_zero X V E hE)
      (supportedTensor_restriction_zero X V _ hr) _)


/-- Restrict supported direct images, including a derived tensor input, to an open.
Source: Stacks Project, Tag 08EV, support reduction; Tag 08DF, supported-open unit;
Tags 08DX and 08DW, compatibility of tensor and pullback with restriction.
(blueprint: lem-pc-supported-open-tensor-direct-image-comparisons).

Proof: put V = X minus T. The supported-open adjunction unit E -> Rj_*(E|_U)
restricts to an isomorphism on U and to a map between zero objects on V, hence
is invertible by detection on this cover. Apply Rf_* and the derived composition
comparison to obtain the first isomorphism. Exact restriction to V annihilates E;
its compatibility with K-flat derived tensor annihilates E tensor Lf^*K as well.
Thus that tensor input also has all cohomology stalks zero outside T. Apply the
same supported-open unit and composition comparison to it. Finally, exact open
restriction commutes with derived tensor, and restriction of Lf^*K agrees with
L(fj)^*K: compose the pullback and restriction adjunctions, transport the right
adjoint along direct-image composition, and use uniqueness of left adjoints.
Apply R(fj)_* to these two identifications for the second isomorphism.
Retain the supplied localizations on X, S and U. Use standard localizations only
on auxiliary complements and inverse-image opens; the restriction homology and
tensor comparisons and open base change allow independent localization universes.
No quasi-coherence, boundedness, properness,
or projection formula is used. Empty opens and zero E give zero comparisons. -/
theorem supportedOpen_tensor_directImage_comparisons
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hE : ∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x)))
    (K : schemeDerivedCategory S) :
    Nonempty ((schemeDerivedDirectImage f).obj E ≅
      (schemeDerivedDirectImage (U.ι ≫ f)).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E)) ∧
    Nonempty ((schemeDerivedDirectImage f).obj (E ⊗ (derivedPullback f).obj K) ≅
      (schemeDerivedDirectImage (U.ι ≫ f)).obj
        (((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⊗
          (derivedPullback (U.ι ≫ f)).obj K)) := by
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : schemeOpenRestriction X U ⊣ G :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  let adj := a.mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨c⟩ := derivedDirectImageComposition U.ι f
  have compare (F : schemeDerivedCategory X)
      (hF : ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor _ n).obj F).val.presheaf x))) :
      Nonempty ((schemeDerivedDirectImage f).obj F ≅
        (schemeDerivedDirectImage (U.ι ≫ f)).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj F)) := by
    have := supportedTensor_supported_unit_iso X U T hT hTU adj F hF
    exact ⟨(schemeDerivedDirectImage f).mapIso (asIso (adj.unit.app F)) ≪≫
      (c.app _).symm⟩
  obtain ⟨e⟩ := compare (E ⊗ (derivedPullback f).obj K)
    (supportedTensor_tensor_support X T hT E _ hE)
  obtain ⟨t⟩ := derivedTensor_openRestriction_iso_universes X U E ((derivedPullback f).obj K)
  obtain ⟨af⟩ := nonempty_derivedPullbackAdjunction f
  obtain ⟨ajf⟩ := nonempty_derivedPullbackAdjunction (U.ι ≫ f)
  let p : derivedPullback f ⋙ (schemeOpenRestriction X U).mapDerivedCategory ≅
      derivedPullback (U.ι ≫ f) :=
    ((af.comp adj).ofNatIsoRight c.symm).leftAdjointUniq ajf
  exact ⟨compare E hE, ⟨e ≪≫ (schemeDerivedDirectImage (U.ι ≫ f)).mapIso
    (t ≪≫ tensorIso (Iso.refl _) (p.app K))⟩⟩

end AlgebraicGeometry
