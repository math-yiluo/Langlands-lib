/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Conormal module of the diagonal

Source: Stacks Project, Tags 01R2, 01KJ and 08S2
(blueprint: def-sc-diagonal-conormal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The conormal module of the diagonal of any scheme morphism.
Source: Stacks, Tags 01R2 and 08S2 (blueprint: def-sc-diagonal-conormal).
Use the actual module-sheaf kernel of `O → Δ_* O`, rather than the largest
quasi-coherent ideal contained in that kernel. On any open neighbourhood W where
Δ is closed, this restricts to its ideal I. Tensor pullback is I/I² on X,
so this construction is independent of W, including for nonseparated f. -/
noncomputable def diagonalConormal (f : X ⟶ S) : X.Modules :=
  (Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
    (kernel (SheafOfModules.unitToPushforwardObjUnit
      (pullback.diagonal f).toRingCatSheafHom))

end AlgebraicGeometry
