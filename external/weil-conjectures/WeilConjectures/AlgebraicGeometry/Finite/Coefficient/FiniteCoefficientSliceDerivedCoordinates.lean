/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDerivedConstantCoordinates
import all WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicLisseFixed
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Derived coordinates on a constant-coefficient ringed slice

Source: Stacks Project, Tags 03CY, 093J and 099R.
(blueprint: lem-weil-pbc-finite-coefficient-slice-derived-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- A module-valued presheaf is a module over the constant ring presheaf. -/
private def fixedModulePresheaf {C : Type (t + 1)} [Category.{t} C]
    (B : Type (t + 1)) [CommRing B] (F : Cᵒᵖ ⥤ ModuleCat.{t + 1} B) :
    PresheafOfModules.{t + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of B)) where
  obj := F.obj
  map f := F.map f
  map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
  map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x

/-- A locally bijective constant scalar map gives an equivalence of module sheaves. -/
private theorem fixedScalarRestriction_equivalence
    {C : Type (t + 1)} [Category.{t} C] (J : GrothendieckTopology C)
    (B : Type (t + 1)) [CommRing B] (R : Sheaf J RingCat.{t + 1})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasSheafify J AddCommGrpCat.{t + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}] :
    (ConstantScalarComparison.restriction J B R a).IsEquivalence := by
  let E := ConstantScalarComparison.restriction J B R a
  have : E.Full := (ConstantScalarComparison.restrictionFullyFaithful J B R a).full
  have : E.Faithful := (ConstantScalarComparison.restrictionFullyFaithful J B R a).faithful
  have : E.EssSurj := by
    constructor
    intro F
    let P := fixedModulePresheaf B F.obj
    let adj := PresheafOfModules.sheafificationAdjunction.{t + 1} a
    let η : F ⟶ E.obj ((PresheafOfModules.sheafification.{t + 1} a).obj P) :=
      ⟨{ app U := (adj.unit.app P).app U
         naturality _ _ f := by
           ext x
           exact ConcreteCategory.congr_hom ((adj.unit.app P).naturality f) x }⟩
    have : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify J P.presheaf)
      exact isIso_toSheafify J
        ((sheafCompose J (forget₂ (ModuleCat.{t + 1} B) AddCommGrpCat.{t + 1})).obj F).property
    have hη (U : Cᵒᵖ) : IsIso (η.hom.app U) := by
      have : IsIso ((PresheafOfModules.toPresheaf _).map (adj.unit.app P)) := inferInstance
      have : IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U) :=
        inferInstance
      rw [← isIso_iff_of_reflects_iso _
        (forget₂ (ModuleCat.{t + 1} B) AddCommGrpCat.{t + 1})]
      change IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U)
      infer_instance
    have : IsIso η := by
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
      change IsIso η.hom
      rw [NatTrans.isIso_iff_isIso_app]
      exact hη
    exact ⟨(PresheafOfModules.sheafification.{t + 1} a).obj P, ⟨(asIso η).symm⟩⟩
  exact {}

/-- Isomorphism classes on the ringed slice can be read in fixed coordinates. -/
private theorem sliceCoordinate_iso_iff
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) (hψ : IsIso ψ) (W : X.Etale)
    (K J : DerivedCategory (SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
        ((toProEt X).obj W) K ≅
      ringedSiteDerivedRestrictionOfUniverses
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
        ((toProEt X).obj W) J) ↔
    Nonempty ((finiteCoefficientSliceRestriction X B R ψ W).mapDerivedCategory.obj K ≅
      (finiteCoefficientSliceRestriction X B R ψ W).mapDerivedCategory.obj J) := by
  classical
  have := hψ
  let U := (toProEt X).obj W
  let D := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let R₀ := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let α := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ
  have : IsIso α := inferInstance
  have : IsIso α.hom := inferInstance
  have : IsIso (Functor.whiskerLeft (Over.forget U).op α.hom) := inferInstance
  let a := Functor.whiskerLeft (Over.forget U).op
    (proEtaleModuleScalarUnit X B ≫ α.hom)
  have : Presheaf.IsLocallyInjective ((ProEt.topology X).over U)
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit X B)) :=
    (proEtaleConstantRingUnit_over_locallyBijective X B U).1
  have : Presheaf.IsLocallySurjective ((ProEt.topology X).over U)
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit X B)) :=
    (proEtaleConstantRingUnit_over_locallyBijective X B U).2
  have : Presheaf.IsLocallyInjective ((ProEt.topology X).over U) a := by
    change Presheaf.IsLocallyInjective _
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit X B) ≫
        Functor.whiskerLeft (Over.forget U).op α.hom)
    infer_instance
  have : Presheaf.IsLocallySurjective ((ProEt.topology X).over U) a := by
    change Presheaf.IsLocallySurjective _
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit X B) ≫
        Functor.whiskerLeft (Over.forget U).op α.hom)
    infer_instance
  let F := ConstantScalarComparison.restriction
    ((ProEt.topology X).over U) (ULift.{t + 1} B) (R₀.over U) a
  have : F.IsEquivalence := fixedScalarRestriction_equivalence _ _ _ _
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology U.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let E := (ProEt.sliceEquiv X U).sheafCongr
    ((ProEt.topology X).over U) (ProEt.topology U.left) D
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let G := F ⋙ E.functor
  have : G.IsEquivalence := inferInstance
  have : G.Additive := inferInstance
  let O := SheafOfModules.overFunctor.{t + 1} R₀ U
  have : O.Additive := (ringedOverFunctor_exactGeneral R₀ U).1
  have : PreservesFiniteLimits O := (ringedOverFunctor_exactGeneral R₀ U).2.1
  have : PreservesFiniteColimits O := (ringedOverFunctor_exactGeneral R₀ U).2.2
  let H := finiteCoefficientSliceRestriction X B R ψ W
  have : H.Additive := (finiteCoefficientSliceRestriction_exact X B R ψ W).1
  have : PreservesFiniteLimits H :=
    (finiteCoefficientSliceRestriction_exact X B R ψ W).2.1
  have : PreservesFiniteColimits H :=
    (finiteCoefficientSliceRestriction_exact X B R ψ W).2.2
  let c : O ⋙ G ≅ H := NatIso.ofComponents (fun M ↦
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _)))
  let r (Z : DerivedCategory (SheafOfModules.{t + 1} R₀)) :
      O.mapDerivedCategory.obj Z ≅ ringedSiteDerivedRestrictionOfUniverses R₀ U Z :=
    O.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫
      O.mapDerivedCategoryFactors.app _
  let e (Z : DerivedCategory (SheafOfModules.{t + 1} R₀)) :
      G.mapDerivedCategory.obj (ringedSiteDerivedRestrictionOfUniverses R₀ U Z) ≅
        H.mapDerivedCategory.obj Z :=
    G.mapDerivedCategory.mapIso (r Z).symm ≪≫
      (Functor.mapDerivedCategoryCompIso O G).app Z ≪≫
      (Functor.mapDerivedCategoryNatIso c).app Z
  constructor
  · rintro ⟨f⟩
    exact ⟨(e K).symm ≪≫ G.mapDerivedCategory.mapIso f ≪≫ e J⟩
  · rintro ⟨f⟩
    exact ⟨G.mapDerivedCategory.preimageIso (e K ≪≫ f ≪≫ (e J).symm)⟩

/-- Changing from ringed slice modules to fixed coefficients preserves and reflects
isomorphism classes of derived objects, and identifies constant realizations.
There is no finiteness, boundedness, covering or etale-origin assertion here.

Source: Stacks Project, modules on sites, change of rings (03CY), module
sheafification (093J), and localization of the pro-etale site (099R).
(blueprint: lem-weil-pbc-finite-coefficient-slice-derived-coordinates).

Proof: on the slice at W restrict the action along the restriction of psi. Its
inverse is restriction along psi inverse, so this is an exact equivalence.
Restrict next along the locally bijective map from the constant B presheaf to
the constant ring sheaf. Module sheafification is its inverse: the unit and
counit are invertible because the underlying additive presheaves are sheaves.
Finally use the equivalence between the pro-etale slice at W and the pro-etale
site of W.left. Their composite E is an additive exact equivalence and
E composed with slice restriction is finiteCoefficientSliceRestriction.
Pass this natural identification and the equivalence to derived categories;
use the factors isomorphism to identify representative-based restriction.
This proves the first assertion. For the second assertion, extension along
psi cancels the first scalar restriction. The sheafification adjunction identifies
the restriction of a constant module realization with the constant module-valued
sheaf. Localization takes a constant sheaf to the constant sheaf. These
identifications are natural in every module, hence commute with all complex
differentials, and descend through quasi-isomorphisms. Exactness of extension
along an isomorphism identifies its left derived functor with termwise extension.
The resulting comparison is the second assertion, for arbitrary unbounded F.
Empty sites and zero rings are included since these equivalences and their
units and counits impose no nonemptiness assumption. -/
theorem finiteCoefficient_slice_derived_coordinates
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (ψ : adicConstantRing X B ⟶ R) (hψ : IsIso ψ) (W : X.Etale) :
    let R₀ := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let H := finiteCoefficientSliceRestriction X B R ψ W
    (∀ K J : DerivedCategory (SheafOfModules.{t + 1} R₀),
      Nonempty (ringedSiteDerivedRestrictionOfUniverses R₀ ((toProEt X).obj W) K ≅
        ringedSiteDerivedRestrictionOfUniverses R₀ ((toProEt X).obj W) J) ↔
      Nonempty (H.mapDerivedCategory.obj K ≅ H.mapDerivedCategory.obj J)) ∧
    ∀ F : DerivedCategory (ModuleCat.{t} B), Nonempty
      (H.mapDerivedCategory.obj ((completedAdicDerivedChange X ψ).obj
        ((finitePerfectAdicDerivedConstant X B).obj F)) ≅
      (constantSheaf (ProEt.topology W.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapDerivedCategory.obj
          ((finitePerfectAdicAlgebraLift B).obj F)) := by
  exact ⟨sliceCoordinate_iso_iff X B R ψ hψ W,
    finiteCoefficient_derived_constant_coordinates X B R ψ hψ W⟩

end AlgebraicGeometry.Scheme
