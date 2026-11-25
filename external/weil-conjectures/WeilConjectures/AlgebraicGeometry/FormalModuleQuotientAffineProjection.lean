/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientAffineProjectionSurjective
import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientAffineProjectionKernel

/-!
# Affine sections of the explicit formal quotient projection

Source: Stacks Project, Tags 01I8, 01IC and 087W, affine module correspondence.
(blueprint: lem-weil-pbc-formal-module-quotient-affine-projection).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- On an affine spectrum the actual sheaf quotient projection is surjective and has
kernel the ideal power times the original module. No completeness or finiteness is needed.
Source: Stacks Project, Tags 01I8, 01IC and 087W, affine module correspondence.
(blueprint: lem-weil-pbc-formal-module-quotient-affine-projection).

Proof: The tilde unit identifies M with the global sections of its associated sheaf.
The ideal sheaf associated with I has global ideal I after transport by ΓSpecIso.
Induct on the positive exponent to identify the range of the power inclusion with I^m:
the first power is J.toModulesι, and each successor is the image of multiplication by J.
The affine tensor-sections comparison identifies the range of multiplication of this
power with the tilde module as I^m times all sections. The product and its cokernel are
quasi-coherent. Exactness of affine sections on quasi-coherent modules says the cokernel
projection is surjective with kernel this range. Transport through the tilde unit gives
the asserted surjectivity and kernel equality. At I=bottom the kernel is zero; at I=top
the quotient is zero. The zero module causes no exception. -/
theorem formalModuleQuotient_affine_projection
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (M : ModuleCat.{u} A) (m : ℕ) (hm : 0 < m) :
    let p := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app M ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (formalModuleQuotientπ J m ((tilde.functor (CommRingCat.of A)).obj M))
    Function.Surjective p ∧ LinearMap.ker p.hom = I ^ m • (⊤ : Submodule A M) := by
  dsimp
  exact ⟨formalModuleQuotient_affine_projection_surjective A I J hJ M m hm,
    formalModuleQuotient_affine_projection_kernel A I J hJ M m hm⟩

end AlgebraicGeometry
