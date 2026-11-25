/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization

import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientExchangeInvertible
import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteScalarMateNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportRationalScalarIso

/-! # Normalized compact-support comparisons for individual coefficient inclusions

Source: main-20261015, lem-weil-compact-support-finite-field-independence, first sentence;
proposition-six-operations-change-coefficients, compact-support and final paragraphs
(blueprint: lem-weil-compact-support-normalized-scalar-isomorphisms).

## Main definitions and statements

- `sfCompactSupportScalarSystemMap`: the actual whole-system mate followed by its limit.
- `sfCompactSupportNormalizedScalarIsomorphisms`: integral and raw rational comparisons,
  with the mixed-unit mate and whole-system normalization for one inclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Transport the given base-field unit through global sections to each residue field.
This is data obtained from the given unit, not an additional invertibility hypothesis.
Source: lem-weil-compact-support-finite-field-independence, coefficient convention
(blueprint: lem-weil-compact-support-normalized-scalar-isomorphisms). -/
@[instance_reducible] def sfCompactSupportScalarResidueUnit
    (W : Scheme.{u}) [W.Over (Spec (.of K₀))] (x : W) :
    Invertible (l : W.residueField x) :=
  let φ := ((Scheme.ΓSpecIso (.of K₀)).inv ≫
    (W ↘ Spec (.of K₀)).appTop ≫ W.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ l)) (hl.map φ)).invertible

end WeilConjectures
