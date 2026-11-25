/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.ConstructibleSheaf.ConstantFiniteMatrixDualKernelAux

/-! # Constant finite matrix dual kernels

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring, finite free transpose argument.
(blueprint: lem-weil-pbc-constant-finite-matrix-dual-kernel)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

/-- The kernel of the sheaf dual of a finite free matrix is constant with its module kernel.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring, finite free transpose argument.

Proof: A finite free module is a finite biproduct of copies of the coefficient ring.
Constant sheafification preserves those biproducts and carries the coefficient ring
with its tensor unit constraint to the sheaf tensor unit. The tensor-Hom adjunction
identifies the dual of a finite biproduct of units with the same finite biproduct of
units. Use the dual basis to identify it with the constant sheaf of the module dual.
These identifications commute with a matrix g: precomposition evaluated at its j-th
basis vector is the sum of the matrix coefficients times the corresponding dual
coordinates. Thus the sheaf dual map becomes the constant sheafification of g.dualMap.
Transport its kernel along this commuting square. Constant sheafification preserves
finite limits, so this kernel is the constant sheaf of the module kernel. The categorical
module kernel is isomorphic to the submodule ker(g.dualMap), giving the conclusion.
The same argument allows either rank to be zero, the zero ring, and the empty scheme.
No finite generation or presentation assertion about an arbitrary module is used here.
(blueprint: lem-weil-pbc-constant-finite-matrix-dual-kernel) -/
theorem nonempty_constantFiniteMatrixDualKernelIso
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ]
    (n m : ℕ) (g : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) :
    Nonempty (kernel
      ((MonoidalClosed.internalHom.flip.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            (ModuleCat.ofHom g)).op) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (LinearMap.ker g.dualMap))) := by
  obtain ⟨e⟩ := constantFiniteMatrixDualKernelIso_aux X n m g
  exact ⟨e ≪≫
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (ModuleCat.kernelIsoKer (ModuleCat.ofHom g.dualMap))⟩

end AlgebraicGeometry.Scheme
