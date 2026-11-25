/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointProperties
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Small classes of restrictions of perfect objects

Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tag 08DR
(blueprint: lem-perfect-restriction-classes-small).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a chosen localization along an exact equivalence of abelian categories.
This is the localization construction in `SchemeIsoDerivedLocalizations`, specialized
to the module-sheaf universe; its helper there is private. -/
private theorem hasDerivedCategory_of_equivalence_private {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact open restriction is derived pullback, hence preserves perfectness (Stacks 09UA). -/
private theorem perfect_exactOpenRestriction (Y : Scheme.{u}) (A : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))]
    [∀ V : A.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings A.toScheme.toRingedSpace).over V))]
    (R' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))
    [R'.Additive] [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
    (hR' : R' = SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) A ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over A))
        (D := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))
        (Modules.overEquiv A))
    (E : schemeDerivedCategory Y) (hE : IsPerfect Y E) :
    IsPerfect A.toScheme (R'.mapDerivedCategory.obj E) := by
  classical
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let C := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace)
  let T : B ⥤ C := Modules.tensorPullback A.ι
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec A.ι
  have h : F = T := CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let η : T ≅ Modules.restrictFunctor A.ι :=
    (Modules.nonempty_tensorPullbackAdjunction A.ι).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction A.ι) ≪≫
        (Modules.restrictFunctorIsoPullback A.ι).symm
  let θ : R' ≅ T := eqToIso hR' ≪≫ Modules.overFunctorEquiv A ≪≫ η.symm
  have : Limits.PreservesFiniteLimits T :=
    Limits.preservesFiniteLimits_of_natIso θ
  have : Limits.PreservesFiniteColimits T :=
    Limits.preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have : (derivedPullback A.ι).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback A.ι ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback A.ι) ε
      T.mapDerivedCategoryFactorsh.hom W
  let c := (Functor.mapDerivedCategoryNatIso θ).app E ≪≫ i.symm.app E
  have hp := derivedPullback_preserve_perfect A.ι E hE
  intro x
  obtain ⟨V, hx, K, hK, ⟨iK⟩⟩ := hp x
  refine ⟨V, hx, K, hK, ?_⟩
  exact ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings A.toScheme.toRingedSpace) V).mapDerivedCategory.mapIso c ≪≫ iK⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smallness on an open bounds the restriction classes of perfect objects on a larger open.
Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tag 08DR
(blueprint: lem-perfect-restriction-classes-small).

Proof: The composite j : (f⁻¹W).toScheme → Y → X is an open immersion.
Its image is f.opensRange ∩ W = W, using hW. Module sheaves on (f⁻¹W).toScheme
are equivalent to module sheaves on the localized site of Y at f⁻¹W, via
Modules.overEquiv. Transport the given derived category across this abelian
equivalence: first use a standard localization on the open scheme, whose derived
category is equivalent to the given localization of the localized module category.
It is locally w-small, so hasLocalizationOfLocallySmall provides a localization
in universe w. For each open of (f⁻¹W).toScheme, its image in Y lies below f⁻¹W;
the over-site equivalence and the equivalence between successive over sites and
the single over site at this image transport the given local structures the same way.
Apply pW to j with these structures to get a u-small perfect quasi-coherent skeleton.
For a perfect quasi-coherent E on Y, exact restriction commutes with homology and
preserves quasi-coherence. Its restriction is perfect: intersect its strictly perfect
neighbourhoods with f⁻¹W, use the iterated restriction isomorphism, and restrict the
bounded finite-free retract data. Transport to the open scheme. Thus its restriction
belongs to that perfect quasi-coherent subcategory. Choose the skeleton representative
of each such restriction and transport it back via the derived over-site equivalence.
The inclusion of the restriction family into the ambient localized derived category
is fully faithful. Its induced map on skeletons is injective, with image contained in
the range of the map from the small perfect skeleton on the open scheme. Therefore
small_of_injective applied into that small range proves the assertion. This concerns
only restrictions, without direct images or triangles. Empty W gives the zero class;
W = f.opensRange is the identity restriction case. -/
theorem perfectRestriction_classes_small (X : Scheme.{u}) (W : X.Opens)
    (pW : PerfectComplexClassesSmallOnOpen.{u, w} X W)
    (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f] (hW : W ≤ f.opensRange)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ A : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over A))] :
    Small.{u} (Skeleton (perfectGluingRestrictionProperty Y (f ⁻¹ᵁ W)).FullSubcategory) := by
  classical
  let A := f ⁻¹ᵁ W
  let B := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over A)
  let C := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace)
  let e : B ≌ C := Modules.overEquiv A
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨hD⟩ := hasDerivedCategory_of_equivalence_private e.symm
  let : HasDerivedCategory.{w} C := hD
  obtain ⟨hO⟩ := nonempty_derivedOpenLocalization A.toScheme
  let : ∀ V : A.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings A.toScheme.toRingedSpace).over V)) := hO
  have hj : (A.ι ≫ f).opensRange = W := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    exact (f.image_preimage_eq_opensRange_inf W).trans (inf_eq_right.mpr hW)
  let P := perfectGluingRestrictionProperty Y A
  let Q : ObjectProperty (schemeDerivedQCohCategory A.toScheme) :=
    fun E ↦ IsPerfect A.toScheme E.obj
  have : Small.{u} (Skeleton Q.FullSubcategory) := pW A.toScheme (A.ι ≫ f) hj
  let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) A
  have : Limits.PreservesFiniteLimits (R ⋙ e.functor) :=
    Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteColimits (R ⋙ e.functor) :=
    Limits.comp_preservesFiniteColimits _ _
  let d := e.mapDerivedCategory
  have hImage (Z : P.FullSubcategory) :
      schemeDerivedQCohProperty A.toScheme (d.functor.obj Z.obj) ∧
        IsPerfect A.toScheme (d.functor.obj Z.obj) := by
    obtain ⟨E, hE, ⟨i⟩⟩ := Z.property
    let c : (R ⋙ e.functor).mapDerivedCategory.obj E.obj ≅ d.functor.obj Z.obj :=
      ((Functor.mapDerivedCategoryCompIso R e.functor).app E.obj).symm ≪≫ d.functor.mapIso i
    have hqc : schemeDerivedQCohProperty A.toScheme
        ((R ⋙ e.functor).mapDerivedCategory.obj E.obj) :=
      (schemeDerivedQCoh_openRestriction_iff Y A E.obj).2 (fun n ↦ by
        have := E.property n
        exact SheafOfModules.isQuasicoherent_over ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E.obj) A)
    have hp := perfect_exactOpenRestriction Y A (R ⋙ e.functor) rfl E.obj hE
    constructor
    · intro n
      exact (SheafOfModules.isQuasicoherent (moduleRings A.toScheme.toRingedSpace)).prop_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso c) (hqc n)
    · intro x
      obtain ⟨V, hx, K, hK, ⟨iK⟩⟩ := hp x
      refine ⟨V, hx, K, hK, ?_⟩
      exact ⟨((SheafOfModules.overFunctor.{u}
        (moduleRings A.toScheme.toRingedSpace) V).mapDerivedCategory.mapIso c).symm ≪≫ iK⟩
  let F := (schemeDerivedQCohProperty A.toScheme).lift (P.ι ⋙ d.functor)
    (fun Z ↦ (hImage Z).1)
  let G := Q.lift F (fun Z ↦ (hImage Z).2)
  exact small_of_injective G.mapSkeleton_injective

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
/-- Public export of the private `hasDerivedCategory_of_equivalence_private` (used by `import all`
importers; linter.privateModule). -/
alias hasDerivedCategory_of_equivalence := hasDerivedCategory_of_equivalence_private

end AlgebraicGeometry.Scheme
