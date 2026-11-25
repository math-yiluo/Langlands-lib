/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Constructed derived stalk comparison for open immersions

Source: Stacks Project, Tags 0098 and 0D5U: exact open restriction and stalks.
(blueprint: def-pc-open-derived-stalk-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The existing exact restriction functor with the shared module-category spelling.
Source: Stacks Project, Tag 0D5U. (blueprint: def-pc-open-derived-stalk-iso). -/
noncomputable abbrev openRestrictionFunctor {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.restrictFunctor j

/-- Finite-limit preservation of the existing open restriction, from sectionwise limits.
Source: Stacks Project, Tag 0D5U. (blueprint: def-pc-open-derived-stalk-iso). -/
instance openRestrictionFunctor_limits {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteLimits (openRestrictionFunctor j) := by
  have : PreservesLimitsOfSize.{u, u} (openRestrictionFunctor j) :=
    Scheme.Modules.preservesLimitsOfSize_restrictFunctor j
  infer_instance

/-- Finite-colimit preservation of open restriction, from its adjunction to pushforward.
Source: Stacks Project, Tag 0D5U. (blueprint: def-pc-open-derived-stalk-iso). -/
instance openRestrictionFunctor_colimits {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteColimits (openRestrictionFunctor j) := by
  have : (openRestrictionFunctor j).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction j).isLeftAdjoint
  infer_instance

/-- Additivity of open restriction, from its sectionwise action on module morphisms.
Source: Stacks Project, Tag 0D5U. (blueprint: def-pc-open-derived-stalk-iso). -/
instance openRestrictionFunctor_additive {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (openRestrictionFunctor j).Additive where
  map_add := by
    intro M N a b
    ext U x
    rfl

/-- Identify derived tensor pullback along an open immersion with exact restriction.
The two underived left adjoints are identified by their adjunctions to pushforward;
the left-derived universal property then determines the derived identification.
Source: Stacks Project, Tag 0D5U. (blueprint: def-pc-open-derived-stalk-iso). -/
noncomputable def openDerivedRestrictionIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    derivedPullback j ≅ (openRestrictionFunctor j).mapDerivedCategory := by
  classical
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback j
  let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := openRestrictionFunctor j
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition.{u, w}) j
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) j
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback j).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) j
  let θ : T ≅ R :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction j) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback j).symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ.symm
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback j) ε
    T.mapDerivedCategoryFactorsh.hom W ≪≫ Functor.mapDerivedCategoryNatIso θ

/-- Canonical representing isomorphism for the literal restriction of a complex.
Its factors are the exact-restriction localization comparison and the inverse of
`openDerivedRestrictionIso`; no representative is selected by an existence proof.
Source: Stacks Project, Tag 0D5U. (blueprint: def-pc-open-derived-stalk-iso). -/
noncomputable def openRestrictionRepresentativeIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj P) ≅
      (derivedPullback j).obj (DerivedCategory.Q.obj P) := by
  let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := openRestrictionFunctor j
  exact R.mapDerivedCategoryFactors.symm.app P ≪≫
    (openDerivedRestrictionIso j).symm.app (DerivedCategory.Q.obj P)

/-- Forgetting scalars in derived stalk cohomology agrees with taking the additive
stalk of the sheaf homology. This is the exact-stalk homology comparison, not a choice
of an isomorphism from an existence statement.
Source: Stacks Project, Tags 01AF and 01AG.
(blueprint: def-pc-open-derived-stalk-iso). -/
noncomputable def additiveStalkCohomologyIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) (y : Y) (i : ℤ) :
    comparisonStalkCohomology Y y i ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u} ≅
      DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i ⋙
        Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  exact Functor.isoWhiskerRight
    ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapDerivedCategoryHomologyFunctorIso
      i).symm (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u})

/-- The natural additive derived stalk identification along any open immersion.
It is constructed from exact-stalk homology, the restriction-stalk isomorphism,
exact-restriction homology, and the universal comparison with derived pullback.
It is independent of any complex or representing isomorphism.
Source: Stacks Project, Tags 0098 and 0D5U.
(blueprint: def-pc-open-derived-stalk-iso). -/
noncomputable def openDerivedStalkIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (i : ℤ) :
    comparisonStalkCohomology Y (j x) i ⋙
        forget₂ (ModuleCat.{u} (Y.presheaf.stalk (j x))) AddCommGrpCat.{u} ≅
      derivedPullback j ⋙ comparisonStalkCohomology X x i ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} := by
  let R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := openRestrictionFunctor j
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i
  let st := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let HU := comparisonStalkCohomology X x i ⋙
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  exact additiveStalkCohomologyIso Y (j x) i ≪≫
    Functor.isoWhiskerLeft H (Scheme.Modules.restrictStalkNatIso j x).symm ≪≫
    Functor.isoWhiskerRight
      (R.mapDerivedCategoryHomologyFunctorIso i) st ≪≫
    Functor.isoWhiskerLeft R.mapDerivedCategory
      (additiveStalkCohomologyIso X x i).symm ≪≫
    Functor.isoWhiskerRight (openDerivedRestrictionIso j).symm HU

end AlgebraicGeometry.SingleComplexBaseChange
