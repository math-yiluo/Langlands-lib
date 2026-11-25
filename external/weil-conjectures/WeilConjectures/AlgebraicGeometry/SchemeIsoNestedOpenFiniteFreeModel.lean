/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Transport of a finite-free model from a nested open

Source: Stacks Project, Tags 08EE and 08E7, identification with an affine spectrum and
restriction of local models (blueprint: lem-pc-scheme-iso-nested-open-finite-free-model).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Transport a complex model through an exact functor square before specializing to sheaves.
private theorem nestedOpenModel_localizationIso
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (R : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃) (F : C₃ ⥤ C₄) (L : C₀ ⥤ C₄)
    [R.Additive] [G.Additive] [H.Additive] [F.Additive] [L.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (c : ((R ⋙ G) ⋙ H) ⋙ F ≅ L)
    (C : CochainComplex C₁ ℤ) (D : CochainComplex C₀ ℤ) (P : CochainComplex C₃ ℤ)
    (hC : C ≅ (R.mapHomologicalComplex (.up ℤ)).obj D)
    (hiso : H.mapDerivedCategory.obj (G.mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj P) :
    Nonempty (L.mapDerivedCategory.obj (DerivedCategory.Q.obj D) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let eC : (G.mapHomologicalComplex (.up ℤ)).obj C ≅
      ((R ⋙ G).mapHomologicalComplex (.up ℤ)).obj D :=
    (G.mapHomologicalComplex (.up ℤ)).mapIso hC ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).app D
  let eH : (H.mapHomologicalComplex (.up ℤ)).obj
      ((G.mapHomologicalComplex (.up ℤ)).obj C) ≅
      (((R ⋙ G) ⋙ H).mapHomologicalComplex (.up ℤ)).obj D :=
    (H.mapHomologicalComplex (.up ℤ)).mapIso eC ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl ((R ⋙ G) ⋙ H)) (.up ℤ)).app D
  let q : DerivedCategory.Q.obj
      ((((R ⋙ G) ⋙ H).mapHomologicalComplex (.up ℤ)).obj D) ≅ DerivedCategory.Q.obj P :=
    DerivedCategory.Q.mapIso eH.symm ≪≫
      (H.mapDerivedCategoryFactors.app _).symm ≪≫
      H.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app C).symm ≪≫ hiso
  exact ⟨L.mapDerivedCategoryFactors.app D ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).app D).symm ≪≫
    (F.mapDerivedCategoryFactors.app _).symm ≪≫
    F.mapDerivedCategory.mapIso q ≪≫ F.mapDerivedCategoryFactors.app P⟩

set_option backward.isDefEq.respectTransparency false in
/-- Transport one specified bounded-above finite-free model on a nested open across a
scheme isomorphism. Neither scheme is assumed affine, and no module localization is used.

Source: Stacks Project, Tags 08EE and 08E7, the passage to an affine spectrum and the
restriction of a local finite-free model
(blueprint: lem-pc-scheme-iso-nested-open-finite-free-model).

Proof: Let Z be the image of V under the open immersion V.toScheme into X, and let W be
its image under s.hom. The composite is an open immersion and induces an isomorphism
V.toScheme with W.toScheme. The membership equivalence is exactly the description of
these two images. Pass P from the localized site over V to modules on V.toScheme using
Modules.overEquiv, restrict along the inverse of this isomorphism, and pass back to the
site over W using its inverse overEquiv. Apply these functors termwise to define P'.
These are exact equivalences, so they preserve zero objects and the given upper bound.
They identify the rank-one free module with the rank-one free module: on sections this
is the structure-sheaf comparison of the scheme isomorphism. Equivalences preserve
coproducts, so the same comparison identifies every free sheaf on ULift (Fin r).
Applying it to each term gives the asserted finite ranks. Localize the exact functors.
The restriction composition comparison identifies restriction first to U and then to V
with restriction to Z. The isomorphism hC identifies C with the restriction of D along s.
Naturality of restriction and the localization factorization comparisons therefore turn
the supplied model isomorphism into the asserted isomorphism over W. Independent choices
of derived categories cause no change: the localized equivalences and their factorization
isomorphisms compare them. This construction also works for empty V, zero ranks and an
arbitrary integer upper bound; it uses no compactness or finite cover. -/
theorem exists_scheme_iso_nested_open_finite_free_model
    {X Y : Scheme.{u}} (s : X ≅ Y) (U : X.Opens)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (D : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hC : Nonempty (C ≅
      ((Modules.restrictFunctor s.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj D))
    (V : U.toScheme.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings U.toScheme.toRingedSpace).over V) (ULift.{u} (Fin r))))
    (hiso : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≅
        DerivedCategory.Q.obj P)) :
    ∃ W : Y.Opens,
      (∀ y : X, s.hom y ∈ W ↔ ∃ hy : y ∈ U, (⟨y, hy⟩ : U.toScheme) ∈ V) ∧
      ∃ P' : CochainComplex
          (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W)) ℤ,
        (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P'.X i)) ∧
        (∀ i : ℤ, ∃ r : ℕ, Nonempty (P'.X i ≅ SheafOfModules.free
          (R := (moduleRings Y.toRingedSpace).over W) (ULift.{u} (Fin r)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings Y.toRingedSpace) W).mapDerivedCategory.obj
            (DerivedCategory.Q.obj D) ≅ DerivedCategory.Q.obj P') := by
  classical
  let j := U.ι ≫ s.hom
  let W := j ''ᵁ V
  -- Free modules and the derived functors share these sheafification instances.
  let : HasSheafify ((Opens.grothendieckTopology U.toScheme.toRingedSpace).over V)
      AddCommGrpCat.{u} := inferInstance
  let : HasSheafify ((Opens.grothendieckTopology Y.toRingedSpace).over W)
      AddCommGrpCat.{u} := inferInstance
  let : ((Opens.grothendieckTopology U.toScheme.toRingedSpace).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  let : ((Opens.grothendieckTopology Y.toRingedSpace).over W).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  let a := j.isoImage V
  let EV := Modules.overEquiv V
  let EW := Modules.overEquiv W
  let ES := CategoryTheory.Equivalence.mk
    (Modules.restrictFunctor a.inv) (Modules.restrictFunctor a.hom)
    ((Modules.restrictFunctorComp a.hom a.inv).symm ≪≫
      Modules.restrictFunctorCongr a.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
    ((Modules.restrictFunctorComp a.inv a.hom).symm ≪≫
      Modules.restrictFunctorCongr a.inv_hom_id ≪≫ Modules.restrictFunctorId)
  let A := (EV.trans ES).trans EW.symm
  have : A.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full A.functor
  let P' := (A.functor.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨W, ?_, P', ?_, ?_, ?_⟩
  · intro y
    constructor
    · rintro ⟨z, hz, he⟩
      have he' : z.val = y := by
        apply s.hom.isOpenEmbedding.injective
        exact he
      subst y
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hV⟩
      exact ⟨⟨y, hy⟩, hV, rfl⟩
  · obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ A.functor.map_isZero (hN i hi)⟩
  · have unitIso : A.functor.obj
        (SheafOfModules.unit ((moduleRings U.toScheme.toRingedSpace).over V)) ≅
        SheafOfModules.unit ((moduleRings Y.toRingedSpace).over W) :=
      EW.inverse.mapIso ((Modules.restrictFunctor a.inv).mapIso
        (V.sheafOfModulesEquivOverUnit (moduleRings U.toScheme.toRingedSpace)) ≪≫
        Modules.restrictUnitIso a.inv) ≪≫
          W.sheafOfModulesEquivOverInverseUnit (moduleRings Y.toRingedSpace)
    intro i
    obtain ⟨r, ⟨e⟩⟩ := hfree i
    exact ⟨r, ⟨A.functor.mapIso e ≪≫
      (SheafOfModules.mapFreeIso A.functor (ULift.{u} (Fin r)) unitIso.symm).symm⟩⟩
  · let G : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (Modules.overEquiv U).functor
    let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) := Modules.restrictFunctor s.hom
    let GY := R ⋙ G
    let H := SheafOfModules.overFunctor.{u} (moduleRings U.toScheme.toRingedSpace) V
    let L := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) W
    let ER := CategoryTheory.Equivalence.mk R (Modules.restrictFunctor s.inv)
      ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
        Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId).symm
      ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
        Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId)
    have : R.IsEquivalence := ER.isEquivalence_functor
    -- Reuse zero preservation when deriving additivity and mapping complexes.
    have : (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have : (Modules.overEquiv U).functor.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_full _
    have : G.PreservesZeroMorphisms := inferInstance
    have : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
    have : H.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have : L.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    let : Abelian (SheafOfModules.{u}
        ((moduleRings U.toScheme.toRingedSpace).over V)) := inferInstance
    let : Abelian (SheafOfModules.{u}
        ((moduleRings Y.toRingedSpace).over W)) := inferInstance
    have : G.Additive := Functor.additive_of_preserves_binary_products G
    have : R.Additive := Functor.additive_of_preserves_binary_products R
    have : H.Additive := Functor.additive_of_preserves_binary_products H
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    have : A.functor.Additive := inferInstance
    let cG : GY ≅ Modules.restrictFunctor j :=
      Functor.isoWhiskerLeft R (Modules.overFunctorEquiv U) ≪≫
        (Modules.restrictFunctorComp U.ι s.hom).symm
    let c0 : (GY ⋙ H) ⋙ (EV.functor ⋙ ES.functor) ≅ L ⋙ EW.functor :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft GY ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Modules.overFunctorEquiv V) ES.functor) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerRight cG _) _ ≪≫
        Functor.isoWhiskerRight (Modules.restrictFunctorComp V.ι j).symm ES.functor ≪≫
        (Modules.restrictFunctorComp a.inv (V.ι ≫ j)).symm ≪≫
        Modules.restrictFunctorCongr (j.isoImage_inv_ι V) ≪≫
        (Modules.overFunctorEquiv W).symm
    let c : (GY ⋙ H) ⋙ A.functor ≅ L :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c0 EW.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L EW.unitIso.symm ≪≫
          Functor.rightUnitor L
    obtain ⟨hC⟩ := hC
    obtain ⟨hiso⟩ := hiso
    exact nestedOpenModel_localizationIso R G H A.functor L c C D P hC hiso

end AlgebraicGeometry.Scheme
