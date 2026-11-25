/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Cohomological smoothness in canonical comparison coordinates

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-purity-conv,
proposition-exceptional-inverse-image-smooth-morphism, clauses 1--3 (blueprint:
proposition-exceptional-inverse-image-smooth-morphism).

This is the constructible pro-etale definition in etale-origin coordinates. The dualizing
object is comparison pullback of the etale dualizing object. Tensor and base-change maps
are comparison pullbacks of the specified counit mates, not arbitrary endpoint maps.
Every pro-etale Dctf object has an etale origin, so testing all etale representatives
whose images are Dctf tests precisely the original domain, independently of witnesses.
Comparison is fully faithful and monoidal on these objects. Its canonical unit, tensor,
pullback and compact-support comparisons identify these maps with the two transposes
in the node. Thus this uses the transported constructible adjunction, rather than an
ambient pro-etale adjunction. The legacy module imports two incompatible versions of
the inverse-image API; this module uses the published canonical etale maps directly.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the actual coefficient quotient, including its size lift.
Source: blueprint finite purity conventions (blueprint:
proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable instance comparedCoefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The existing Nagata compactification in the finite-type field setting.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, separated finite-type
setting (blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def comparedCompactification (P : PurityFiniteSetting.{u})
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsSeparated f]
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    (aY : Y ⟶ AlgebraicGeometry.Spec (.of P.field.k))
    [AlgebraicGeometry.LocallyOfFiniteType aY] [AlgebraicGeometry.QuasiCompact aY] :
    AlgebraicGeometry.Compactification f :=
  letI := AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian aY
  letI := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace aY
  AlgebraicGeometry.HasCompactification.compactification f

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

/-- The relative dualizing object in its canonical etale-origin model.
It is nu_X^* of f^! of the coefficient unit. This is the canonical unit normalization
of the recorded transported exceptional functor nu_X^* f^! Rnu_Y,*.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, omega_f
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def comparedDualizing (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
    (Etale.dualizingComplex P.Coefficient f)

/-- Tensor invertibility with the inverse in the original pro-etale Dctf category.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 1
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def comparedInvertibilityClause
    (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (ω : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  ∃ M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)),
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X M ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj ω).obj M ≅ 𝟙_ _) ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj ω ≅ 𝟙_ _)

/-- The canonical tensor mate on every etale representative of a pro-etale Dctf object.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 2
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def comparedTensorClause
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] : Prop :=
  ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)),
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj K) →
    IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      (Etale.dualizingComplexTensorMap Λ f K))

/-- The canonical dualizing base-change mate after every finite-type change of base.
The primed compactification is the base change of the specified original one.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 3
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def comparedBaseChangeClause
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] : Prop :=
  ∀ (X' Y' : Scheme.{u}) [X'.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))] (sq : IsPullback g' f' f g),
    letI := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    letI : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    IsIso ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      (Etale.dualizingComplexBaseChangeMap P.Coefficient sq))

/-- The three cohomological-smoothness clauses in canonical comparison coordinates.
Clause 1 uses the actual pro-etale tensor and Dctf predicate. Clause 2 tests the
comparison pullback of the specified tensor mate on every etale representative of
a pro-etale Dctf object. Clause 3 uses the comparison pullback of the specified
compact-support base-change mate, with every finite-type change of base allowed.
The canonical comparison is fully faithful on these representatives and commutes
with pullback, tensor and compact supports, with the specified units and counits;
therefore the two maps are exactly the node's maps in these coordinates. Symmetry
changes the tensor mate's source ordering from pullback tensor omega to omega tensor
pullback. No isomorphism between endpoints is substituted for a canonical map.
Source: blueprint main-20261015, proposition-exceptional-inverse-image-smooth-morphism, clauses 1--3
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def IsCohomologicallySmoothCompared
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  comparedInvertibilityClause P X (comparedDualizing P f) ∧
    comparedTensorClause P.Coefficient f ∧ comparedBaseChangeClause P f

end AlgebraicGeometry.ProEtale
