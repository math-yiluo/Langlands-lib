/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.ConstructibleSheaf.ConstantFiniteMatrixDualKernel

/-! # Dual of a finite constant module sheaf

Source: the finite presentation argument in the docstring of
`WeilConjectures/ConstructibleSheaf/Monoidal.lean`, `IsFiniteLocallyConstantSheaf.ihom_unit`.
(blueprint: lem-weil-pbc-constant-module-dual)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- Over a noetherian coefficient ring, dualizing a constant sheaf with a finite module
value produces the constant sheaf with the module dual as value.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit`, finite presentation argument.

Proof: Since Λ is noetherian, the finite module M has a finite presentation
Λᵐ → Λⁿ → M → 0. The constant sheaf functor is exact and monoidal, so it carries
this to a presentation by finite free coefficient sheaves. Applying internal Hom
into the unit gives the kernel of the transposed map between the finite free duals.
Those duals are again the constant finite free sheaves, and the transposed map is
the constant sheafification of the module transpose. Constant sheafification
preserves kernels. In modules the kernel of this transpose is Hom_Λ(M, Λ), by
applying Hom_Λ(-, Λ) to the presentation. Composing these kernel isomorphisms gives
the claimed isomorphism. No projectivity of M is assumed; for M = 0 the same
argument uses a zero presentation, and the empty scheme causes no exception.
(blueprint: lem-weil-pbc-constant-module-dual) -/
theorem nonempty_constantModuleDualIso
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    Nonempty ((ihom ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj
      (𝟙_ _) ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (M →ₗ[Λ] Λ))) := by
  classical
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' Λ M
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let D := MonoidalClosed.internalHom.flip.obj
    (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  let a : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ) :=
    ModuleCat.ofHom g
  have hker : LinearMap.ker f = LinearMap.range g := LinearMap.exact_iff.mp hgf
  let eM : Limits.cokernel a ≅ M :=
    (Limits.cokernelIsCokernel a).coconePointUniqueUpToIso
      (ModuleCat.isColimitCokernelCofork a (ModuleCat.ofHom f) hgf hf)
  let eC : C.obj M ≅ Limits.cokernel (C.map a) :=
    C.mapIso eM.symm ≪≫ Limits.PreservesCokernel.iso C a
  have hrange : LinearMap.range f.dualMap = LinearMap.ker g.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective f hf,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range, hker]
  let eA : ModuleCat.of Λ (M →ₗ[Λ] Λ) ≅ ModuleCat.of Λ (LinearMap.ker g.dualMap) :=
    ((LinearEquiv.ofInjective f.dualMap (LinearMap.dualMap_injective_of_surjective hf))
      ≪≫ₗ LinearEquiv.ofEq _ _ hrange).toModuleIso
  let eD : D.obj (Opposite.op (C.obj M)) ≅
      Limits.kernel (D.map (C.map a).op) := by
    calc
      D.obj (Opposite.op (C.obj M)) ≅
          D.obj (Opposite.op (Limits.cokernel (C.map a))) := D.mapIso eC.symm.op
      _ ≅ D.obj (Limits.kernel (C.map a).op) :=
        D.mapIso (kernelOpOp (C.map a)).symm
      _ ≅ Limits.kernel (D.map (C.map a).op) :=
        Limits.PreservesKernel.iso D (C.map a).op
  obtain ⟨eF⟩ := nonempty_constantFiniteMatrixDualKernelIso X n m g
  exact ⟨eD ≪≫ eF ≪≫ C.mapIso eA.symm⟩

end AlgebraicGeometry.Scheme
