/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.ConstructibleSheaf.ConstantFiniteFreeDualNaturality

@[expose] public section
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

/-- The finite-free kernel comparison before replacing the categorical module kernel by
the explicit linear kernel.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring. The proof uses the finite biproduct
description of free modules, the monoidal constant sheaf functor, and preservation of
finite kernels. The remaining identification with `LinearMap.ker` is deliberately left
to `ModuleCat.kernelIsoKer` in the parent theorem.
(blueprint: lem-weil-pbc-constant-finite-matrix-dual-kernel-aux) -/
theorem constantFiniteMatrixDualKernelIso_aux
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ]
    (n m : ℕ) (g : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) :
    Nonempty (kernel
      ((MonoidalClosed.internalHom.flip.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            (ModuleCat.ofHom g)).op) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (kernel (ModuleCat.ofHom g.dualMap))) := by
  obtain ⟨e, he⟩ := constantFiniteFreeDualNaturality X (Λ := Λ)
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let D := MonoidalClosed.internalHom.flip.obj
    (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  exact ⟨kernel.mapIso (D.map (C.map (ModuleCat.ofHom g)).op)
    (C.map (ModuleCat.ofHom g.dualMap)) (e n) (e m) (he n m g) ≪≫
      (PreservesKernel.iso C (ModuleCat.ofHom g.dualMap)).symm⟩

end AlgebraicGeometry.Scheme
