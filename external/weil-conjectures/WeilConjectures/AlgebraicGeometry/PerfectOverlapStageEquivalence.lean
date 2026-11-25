/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # The cartesian equivalence for the overlap at a finite stage

Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-stage-equivalence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The exact nested-open restriction agrees with derived pullback along its inclusion.
Source: Stacks Project, Tag 08DW, restriction of derived pullback.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def overlapOpenInclusionPullbackIso (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    derivedPullback (X.homOfLE (leOfHom i)) ≅
      (schemeOpenOverlapRestriction X i).mapDerivedCategory := by
  classical
  let f := X.homOfLE (leOfHom i)
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition) f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let Q := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)
  have : (derivedPullback f).IsLeftDerivedFunctor ε Q :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  let η : T ≅ Scheme.Modules.restrictFunctor f :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let restriction : schemeOpenOverlapRestriction X i ≅ Scheme.Modules.restrictFunctor f :=
    Functor.isoWhiskerLeft (Scheme.Modules.overEquiv U).inverse
        (Scheme.Modules.overMapCompOverEquiv i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).counitIso _ ≪≫ Functor.leftUnitor _
  let θ : schemeOpenOverlapRestriction X i ≅ T := restriction ≪≫ η.symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom Q :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback f) ε
    T.mapDerivedCategoryFactorsh.hom Q ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm

/-- Derived pullback along the inverse of a scheme isomorphism, with its inverse
constructed from pullback along the isomorphism itself.
Source: Stacks Project, Tag 0D5S, composition and identity pullback.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def overlapSchemeIsoDerivedEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    schemeDerivedCategory X ≌ schemeDerivedCategory Y := by
  let identity : ∀ Z : Scheme.{u}, derivedPullback (𝟙 Z) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).2
  exact CategoryTheory.Equivalence.mk (derivedPullback e.inv) (derivedPullback e.hom)
    (perfectHomComposition e.hom e.inv ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) e.hom_inv_id) ≪≫ identity X).symm
    (perfectHomComposition e.inv e.hom ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) e.inv_hom_id) ≪≫ identity Y)

/-- The overlap inverse image is the base change of the original overlap.
The equivalence is constructed from the cartesian open-restriction square.
Source: Stacks Project, Tag 08DW, compatibility with open restriction.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapStageEquivalence
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V : Y.Opens) :
    schemeDerivedCategory (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≌
      schemeDerivedCategory (pullback ((U ⊓ V).ι ≫ p) q) :=
  overlapSchemeIsoDerivedEquivalence
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback

/-- The stage equivalence carries exact restriction of a pulled-back object to
pullback of its restriction on the original overlap.
Source: Stacks Project, Tag 08DW, restriction and composition of pullback.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapStageObjectIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    (derivedPullback (g ∣_ L) ⋙
      (schemeOpenOverlapRestriction X (homOfLE
        (show g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L from fun _ hx ↦ hWL hx))).mapDerivedCategory) ⋙
      (perfectOverlapStageEquivalence g p' p q h U V).functor ≅
    derivedPullback (Y.homOfLE hWL) ⋙
      derivedPullback (pullback.fst ((U ⊓ V).ι ≫ p) q) := by
  let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
  let square := (isPullback_morphismRestrict g (U ⊓ V)).paste_vert h
  let e := square.isoPullback
  have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
      (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl
  have fac : (e.inv ≫ X.homOfLE hW') ≫ (g ∣_ L) =
      pullback.fst ((U ⊓ V).ι ≫ p) q ≫ Y.homOfLE hWL := by
    rw [Category.assoc, restricted, ← Category.assoc]
    rw [square.isoPullback_inv_fst]
  change (derivedPullback (g ∣_ L) ⋙
    (schemeOpenOverlapRestriction X (homOfLE hW')).mapDerivedCategory) ⋙
    derivedPullback e.inv ≅ _
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (overlapOpenInclusionPullbackIso X (homOfLE hW')).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (perfectHomComposition e.inv (X.homOfLE hW')) ≪≫
    perfectHomComposition (e.inv ≫ X.homOfLE hW') (g ∣_ L) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
    (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ p) q) (Y.homOfLE hWL)).symm

/-- The apex equivalence first identifies the localized-open site with the actual
open subscheme, then applies the cartesian overlap equivalence.
Source: Stacks Project, Tags 08DW and 05RU.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapApexEquivalence
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)))] :
    DerivedCategory (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V))) ≌
      schemeDerivedCategory (pullback ((U ⊓ V).ι ≫ p) q) := by
  letI := openComparisonOverModuleAbelian X.toRingedSpace (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
  letI := openComparisonModuleAbelian (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace
  let e : SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)) ≌
      SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv _
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  letI : e.inverse.IsEquivalence := e.isEquivalence_inverse
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact e.mapDerivedCategory.trans
    (perfectOverlapStageEquivalence g p' p q h U V)

/-- The supplied local object isomorphism gives the object comparison at the apex.
Source: Stacks Project, Tag 08DW, restriction of the supplied pullback isomorphism.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapApexObjectIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (A : schemeDerivedCategory L.toScheme) (E : schemeDerivedCategory X)
    (φ : (derivedPullback (g ∣_ L)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ L)).mapDerivedCategory.obj E) :
    (perfectOverlapApexEquivalence g p' p q h U V).functor.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≅
    (derivedPullback (pullback.fst ((U ⊓ V).ι ≫ p) q)).obj
      ((derivedPullback (Y.homOfLE hWL)).obj A) := by
  let W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
  let hW' : W' ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
  letI := openComparisonOverModuleAbelian X.toRingedSpace W'
  letI := openComparisonModuleAbelian W'.toScheme.toRingedSpace
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W') ≌
      SheafOfModules.{u} (moduleRings W'.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv W'
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W'
  let SU := (schemeOpenOverlapRestriction X (homOfLE hW')).mapDerivedCategory
  let cart := perfectOverlapStageEquivalence g p' p q h U V
  change cart.functor.obj (e.functor.mapDerivedCategory.obj (R.mapDerivedCategory.obj E)) ≅ _
  exact cart.functor.mapIso
      ((Functor.mapDerivedCategoryCompIso R e.functor).app E ≪≫
        (schemeDerivedOpenRestrictionCompIso X (homOfLE hW')).symm.app E ≪≫
        SU.mapIso φ.symm) ≪≫
    (perfectOverlapStageObjectIso g p' p q h U V L hWL).app A

end AlgebraicGeometry
