/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Coherent, quasi-coherent and finite-type modules

Source: Stacks Project, Sheaves of Modules, Tags 01BV, 01B5 and 01BE;
Schemes, Tag 01IA (blueprint: pqf-def-coherent).

The public coherence import exposes `RingedSpace.IsCoherent`, the finite-type
and finite-type-kernel condition of Tag 01BV. Mathlib supplies
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`. The landed
`Scheme.Modules.IsQuasiCoherentFiniteType` conjunction is retained unchanged
for its existing consumers; it does not replace the coherence predicate.
-/

@[expose] public section
set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A sheaf of modules is quasi-coherent and of finite type.
Source: Stacks Project, Modules on Schemes, Tags 01B5 and 01BE
(blueprint: pqf-def-coherent). -/
def Scheme.Modules.IsQuasiCoherentFiniteType {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F

end AlgebraicGeometry
