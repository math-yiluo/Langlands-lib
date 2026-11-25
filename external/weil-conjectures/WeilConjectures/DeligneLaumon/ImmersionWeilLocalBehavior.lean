/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ImmersionWeilPullbackLocalBehavior

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.ConstructiblePullbackTExact
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
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
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Immersion operations on constructible Weil pairs

Source: blueprint main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction and Part 2
(blueprint: lem-zl-immersion-weil-local-behavior).

The clause packages retain the canonical underlying comparisons. Weil complexes are
fixed pairs, and no triangulated structure on their category is asserted.

## Main statements

* `immersionWeil_closed_point`: closed images and canonical residue-field isomorphisms.
* `immersionWeil_pullback_local_behavior`: exact pullback and Frobenius-equivariant stalks.
* `immersionWeil_open_local_behavior`: exact open compact support and its stalk formulas.
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

variable (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

include prime hl in
/-- The geometric-fibre map is over the algebraic closure by its second projection.
Source: blueprint base change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilFiberMap_isOver (j₀ : W₀ ⟶ X₀) :
    (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left).IsOver
      (Spec (.of D.k)) :=
  inferInstanceAs ((((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left).IsOver _)

variable (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left]

end WeilConjectures
