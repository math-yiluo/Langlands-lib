/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # A shared presentation of the finite geometric base change

The pullback data do not depend on the finite-type and quasi-compactness witnesses.
Source: latest blueprint, the finite geometric fibre in the evaluation display
(blueprint: def-a1-finite-geometric-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The actual pullback model, with finiteness retained as an explicit parameter.
Source: latest blueprint, geometric fibre over the algebraic closure
(blueprint: def-a1-finite-geometric-model). -/
abbrev finiteGeometricModel (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom] : Over (Spec (.of D.k)) :=
  D.geometricFiber T₀

/-- The shared model has exactly the data of the existing geometric fibre.
Source: latest blueprint, the specified geometric base change
(blueprint: def-a1-finite-geometric-model). -/
theorem finiteGeometricModel_eq (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom] :
    finiteGeometricModel D T₀ = D.geometricFiber T₀ := rfl

end WeilConjectures
