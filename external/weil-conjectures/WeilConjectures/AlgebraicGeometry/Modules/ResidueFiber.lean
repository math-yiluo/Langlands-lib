/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field fibres of scheme modules

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.residueFiber`: the stalk extended to the residue field.
- `AlgebraicGeometry.Scheme.Modules.residueValue`: the value of a section in that fibre.

## References

* Stacks Project, Modules, Tags 01C5 and 01CB
* Sheaves, Tag 0098
* Stacks Project, Modules, Tag 01C5
-/

@[expose] public section

universe u

open CategoryTheory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The fibre `κ(x) ⊗_{O_{X,x}} M_x`, equivalently `M_x ⊗_{O_{X,x}} κ(x)`. -/
def residueFiber {X : Scheme.{u}} (M : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  (ModuleCat.extendScalars (X.residue x).hom).obj
    (ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x))

/-- A section's value in the fibre is its germ tensored with `1`. -/
def residueValue {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) (x : X) (hx : x ∈ U) : residueFiber M x :=
  (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x, (X.residue x).hom]
    M.presheaf.germ U x hx s

end
end AlgebraicGeometry.Scheme.Modules
