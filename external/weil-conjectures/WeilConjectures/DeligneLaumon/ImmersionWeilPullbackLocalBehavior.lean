/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.ConstructiblePullbackTExact
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Topology.JacobsonSpace
import WeilConjectures.ZetaSeries
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportConstructible
import WeilConjectures.DeligneLaumon.ConstructibleTruncations
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Pullback and finite descent for constructible Weil pairs

Source: blueprint main-20261015, Restriction in
`lem-zl-immersion-weil-local-behavior`.

This is the unchanged pullback and descent interface extracted from
`ImmersionWeilLocalBehavior`. It depends on pullback and local Frobenius, so its
consumers can use it before the separate compact-support interface is restored.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genInjectivity false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [prime : Fact l.Prime] (hl : l ≠ D.p)
  (X₀ W₀ : Over (Spec (.of D.k₀)))
  [hftX : LocallyOfFiniteType X₀.hom] [hqcX : QuasiCompact X₀.hom] [hsepX : IsSeparated X₀.hom]
  [hftW : LocallyOfFiniteType W₀.hom] [hqcW : QuasiCompact W₀.hom] [hsepW : IsSeparated W₀.hom]
  (h₀ : W₀ ⟶ X₀) [himm : IsImmersion h₀.left]

/-- The finite-type structure on the actual geometric fibre is inherited by base change.
Source: blueprint geometric-base-change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilOverPullback_locallyOfFiniteType {B T : Scheme.{u}} (f : T ⟶ B)
    (Y : Over B) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (((Over.pullback f).obj Y).left ↘ T) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd Y.hom f))

/-- Quasi-compactness on a geometric fibre is inherited by base change.
Source: blueprint geometric-base-change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilOverPullback_quasiCompact {B T : Scheme.{u}} (f : T ⟶ B)
    (Y : Over B) [QuasiCompact Y.hom] :
    QuasiCompact (((Over.pullback f).obj Y).left ↘ T) :=
  inferInstanceAs (QuasiCompact (pullback.snd Y.hom f))

variable (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end WeilConjectures
