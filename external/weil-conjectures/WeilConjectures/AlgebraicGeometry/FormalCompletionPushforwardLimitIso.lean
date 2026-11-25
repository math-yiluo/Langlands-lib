/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.FormalCompletionPushforwardLimitAppBijective
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The proper pushforward comparison is invertible on inverse limits

Source: Stacks Project, Theorem 02OC and the first half of Lemma 088B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The supplied canonical comparison induces an isomorphism of limit sheaves.
Source: Stacks Project, Theorem 02OC (degree zero), and Lemma 088B, the paragraph
identifying the inverse limit of the modules M_n with the completion of M.
(blueprint: lem-weil-pbc-formal-completion-pushforward-limit-iso)

Proof: Fix an affine open U = Spec A of Y and set I = J(U), H = f_*F and
M = Gamma(U,H). Restrict f to f^(-1)U; it remains proper, and F remains coherent.
The ideal-product and quasi-coherent quotient section formulas identify the sections
of H/J^(n+1)H with M/I^(n+1)M, compatibly with their quotient projections and
transitions. Pushforward sections on U are sections on f^(-1)U. The equation hκ
therefore identifies the section map of κ_n with the canonical quotient-induced
map in the degree-zero theorem on formal functions: the quotient projection is
surjective, so its equation determines this map. That theorem says the induced
map of A-module limits is an isomorphism. Evaluation of sheaves of modules on U
preserves inverse limits. Consequently evaluation of lim.map κ is an isomorphism
on every affine open. A sheaf map that is invertible on an affine basis is invertible:
the inverses commute with restriction by cancellation and glue on arbitrary opens.
Thus lim.map κ is an isomorphism of sheaves of modules. This makes no claim that
any individual κ_n is invertible. For the zero ideal the systems are constant;
for the unit ideal they are zero. Zero sheaves and the empty scheme give zero limits.
-/
theorem formalCompletion_pushforward_limit_isIso {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) :
    IsIso (lim.map κ) := by
  apply Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen (lim.map κ)
  intro U hU
  exact formalCompletion_pushforward_limit_app_bijective J f F h κ hκ U hU

end AlgebraicGeometry
