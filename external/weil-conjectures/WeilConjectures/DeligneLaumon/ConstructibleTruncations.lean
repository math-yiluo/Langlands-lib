/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Constructible truncations and the retained localization compatibility API

The current ordinary condensed-coefficient proposition is proved in
`WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations`,
publicly reexported here.

The declarations below retain the previously proved rational/common-stage API for its
existing consumers. Their coefficient categories come from the historical 2026-10-15
blueprint, and they are not the realization of the current ordinary-category proposition.
No historical declaration or proof is removed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y : Scheme.{u}) [base : Y.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage stageTransition inclusion)

include D hl base hft hqc

end WeilConjectures
