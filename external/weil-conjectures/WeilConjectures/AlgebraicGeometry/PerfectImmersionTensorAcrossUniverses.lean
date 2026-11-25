/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SmoothProperDiagonalTensorFormula
import WeilConjectures.AlgebraicGeometry.DerivedLocalizationTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedQCohStandardAdjunction
import WeilConjectures.AlgebraicGeometry.PerfectImmersionStandardPerfection
import all Mathlib.Algebra.Homology.Localization

/-! # The perfect immersion tensor formula in independent derived universes

Source: Stacks Project, Tag 0A9U, and uniqueness of localization, Tag 05RU.
(blueprint: lem-sc-perfect-immersion-tensor-across-universes).
-/

@[expose] public section

set_option autoImplicit false

universe u wZ wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Qh comparison identifies the single structure module with the standard tensor unit. -/
private noncomputable def standardUnitComparison (X : Scheme.{u})
    (h : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    (@schemeDerivedStandardEquivalence X h).functor.obj
      ((@DerivedCategory.singleFunctor _ _ _ h 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≅
      𝟙_ (@schemeDerivedCategory X (HasDerivedCategory.standard _)) := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  exact (Localization.compUniqFunctor (@DerivedCategory.Qh A _ _ h)
    (@DerivedCategory.Qh A _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso A (.up ℤ))).app
      ((HomotopyCategory.singleFunctor A 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- The tensor formula for a specified right adjoint of a perfect proper closed immersion.
Source: Stacks Project, Tag 0A9U, the second equality of Tag 0BRT, and Tag 05RU.
(blueprint: lem-sc-perfect-immersion-tensor-across-universes).

Proof: `perfectImmersion_standardPerfection` transfers the perfection hypothesis
and identifies the standard derived pushforward of the tensor unit. The proved
`derivedQCoh_standardAdjunction` conjugates the given adjunction to a standard
one, with natural comparisons of the quasi-coherent objects and right adjoints.
Apply `smooth_proper_diagonal_tensor_formula` to the standard immersion and the
image of K. Its invertible mate gives an isomorphism in the full quasi-coherent
category; apply inclusion and invert it. The Qh comparison identifies the image
of the supplied single structure module with the standard tensor unit. Compose
this with hOP and the quasi-coherent inclusion comparison and map through the
standard right adjoint. Apply the inverse standard comparison to the tensor
formula, then `derivedLocalization_tensorComparison`. The pullback comparison
follows from the definition of `derivedPullbackAcrossUniverses` and the inclusion
comparison for K. The right factor comparison follows from the right-adjoint
comparison for OP and the unit isomorphism of the ambient equivalence. Compose
these isomorphisms to obtain the displayed orientation. No extra hypotheses or
changes of definitions are used. Identity and empty immersions are covered. -/
theorem perfectImmersion_tensor_acrossUniverses
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsProper i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))))
    (hRi : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E.obj))
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adjC : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRi ⊣ c)
    (OP : schemeDerivedQCohCategory Y)
    (hOP : OP.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf))
    (K : schemeDerivedQCohCategory Y) :
    Nonempty ((c.obj K).obj ≅
      (derivedPullbackAcrossUniverses i).obj K.obj ⊗ (c.obj OP).obj) := by
  let hZ : HasDerivedCategory.{wZ}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) := inferInstance
  let hY : HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance
  let hU : ∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) := inferInstance
  let sZ := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let sY := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let sU := fun U : Y.Opens ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))
  let PY := @schemeDerivedQCohProperty Y sY
  let PZ := @schemeDerivedQCohProperty Z sZ
  let L := @derivedPullback Z Y i sY sZ
  let eZ := @schemeDerivedStandardEquivalence Z hZ
  let eY := @schemeDerivedStandardEquivalence Y hY
  obtain ⟨qY, hRiS, cS, ⟨adjS⟩, ⟨ηY⟩, ⟨ηC⟩⟩ :=
    @derivedQCoh_standardAdjunction.{u, wZ, wY} Z Y i
      hZ hY hRi c adjC
  have hperfectS :=
    @perfectImmersion_standardPerfection.{u, wY} Z Y i
      inferInstance hY hU hperfect
  obtain ⟨hRf, hO, hTensor, ⟨mon⟩, ⟨a⟩, formula⟩ :=
    @smooth_proper_diagonal_tensor_formula Z Y inferInstance inferInstance i
      inferInstance inferInstance sZ sY sU hperfectS
  let KS := qY.functor.obj K
  let OS : PY.FullSubcategory := ⟨𝟙_ _, hO⟩
  obtain ⟨pf, _, hm⟩ := formula mon a cS adjS KS
  let m : (⟨L.obj KS.obj ⊗ (cS.obj OS).obj,
      hTensor KS (cS.obj OS)⟩ : PZ.FullSubcategory) ⟶ cS.obj KS :=
    (adjS.homEquiv _ KS)
      (ObjectProperty.homMk (pf.hom ≫
        KS.obj ◁ (adjS.counit.app OS).hom ≫ (ρ_ KS.obj).hom))
  have : IsIso m := hm
  let stdIso : (cS.obj KS).obj ≅ L.obj KS.obj ⊗ (cS.obj OS).obj :=
    (PZ.ι.mapIso (asIso m)).symm
  let hunitY := standardUnitComparison Y hY
  let opIso : qY.functor.obj OP ≅ OS :=
    PY.isoMk ((ηY.app OP) ≪≫ eY.functor.mapIso hOP ≪≫ hunitY)
  let cUnitIso : (cS.obj OS).obj ≅ eZ.functor.obj (c.obj OP).obj :=
    PZ.ι.mapIso (cS.mapIso opIso.symm) ≪≫ ηC.app OP
  obtain ⟨tensorComparison⟩ := @derivedLocalization_tensorComparison.{u, wZ} Z hZ
    (L.obj KS.obj) (cS.obj OS).obj
  let pullbackIso : eZ.inverse.obj (L.obj KS.obj) ≅
      (@derivedPullbackAcrossUniverses Z Y i hZ hY).obj K.obj :=
    eZ.inverse.mapIso (L.mapIso (ηY.app K))
  let rightIso : eZ.inverse.obj (cS.obj OS).obj ≅ (c.obj OP).obj :=
    eZ.inverse.mapIso cUnitIso ≪≫ (eZ.unitIso.app (c.obj OP).obj).symm
  exact ⟨(eZ.unitIso.app (c.obj K).obj) ≪≫
    eZ.inverse.mapIso (ηC.app K).symm ≪≫
    eZ.inverse.mapIso stdIso ≪≫ tensorComparison ≪≫ (pullbackIso ⊗ᵢ rightIso)⟩

end AlgebraicGeometry
