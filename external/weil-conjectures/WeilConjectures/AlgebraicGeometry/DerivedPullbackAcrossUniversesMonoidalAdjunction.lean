/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal
import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-! # Monoidal adjunction for the transported derived pullback

Source: Stacks Project, Tags 079U, 079W and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-monoidal-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The transported K-flat pullback is strong monoidal and left adjoint to the
specified K-injective direct image, with independent localization universes.
Source: Stacks Project, Tags 079U, 079W and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-monoidal-adjunction).

Proof: Use the canonical monoidal model of derived pullback in the standard
localizations, constructed by deriving the module tensor comparison on K-flat
resolutions. The localization equivalences used in
`derivedPullbackAcrossUniverses` are strong monoidal: compare their tensorators
on K-flat representatives with the fixed derived tensor structures, and descend
associativity and unit coherence by the localization universal property.
Transport the standard pullback monoidal model through these equivalences.
For the adjunction, the module pullback is left adjoint to module direct image.
K-flat pullback and K-injective direct image derive this adjunction (079W).
Uniqueness of the left-derived functor identifies its left side with the
standard `derivedPullback`; uniqueness of the right-derived functor identifies
its right side with `schemeDerivedDirectImage`. Transport unit and counit
through the localization equivalences. The triangle identities are preserved
by equivalence and the right-derived uniqueness isomorphism. This gives an
adjunction whose functors are exactly the two specified functors. No scheme
finiteness condition or perfect argument is used. Only existence of structures
is asserted; no object is defined by choosing an unproved existence witness. -/
theorem exists_derivedPullbackAcrossUniverses_monoidal_adjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ m : (derivedPullbackAcrossUniverses f).CoreMonoidal,
      Nonempty (derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f) := by
  classical
  obtain ⟨mY⟩ := exists_schemeDerivedStandardEquivalence_monoidal Y
  obtain ⟨mX⟩ := exists_schemeDerivedStandardEquivalence_monoidal X
  let := mY.toMonoidal
  let := mX.toMonoidal
  let := (schemeDerivedStandardEquivalence X).inverseMonoidal
  obtain ⟨m, _⟩ := @exists_derivedPullbackMonoidalModel X Y f
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  let := m.toMonoidal
  obtain ⟨P, hP, hmap, hAdd, L, ε, hL, _, ⟨a⟩⟩ :=
    RingedSpace.derivedModulePullback_adjunction f.toLRSHom.toShHom
  let := hAdd
  obtain ⟨ε', hL'⟩ := exists_derivedPullbackAcrossUniverses_leftDerived f P hP hmap
  let := hL
  let := hL'
  let e := Functor.leftDerivedUnique (derivedPullbackAcrossUniverses f) L ε ε'
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
  let a' : derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f :=
    a.ofNatIsoLeft e
  refine ⟨?_, ⟨a'⟩⟩
  change ((schemeDerivedStandardEquivalence Y).functor ⋙
    @derivedPullback X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) ⋙ (schemeDerivedStandardEquivalence X).inverse).CoreMonoidal
  exact Functor.CoreMonoidal.ofLaxMonoidal _

end AlgebraicGeometry
