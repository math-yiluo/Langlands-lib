/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine

/-! # The canonical finite Tate pairing in degree zero -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.Etale

-- Keep the large canonical comparison behind a shared, fully constructed arrow.
/-- Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, ordered Tate factors.
(blueprint: def-sp-finite-affine-tate-pairing)

Construction: take the product p of finiteEtaleTwistPullbackData at the nonnegative
exponents r and s, rewrite their sum as the cast of r+s, and reduce the nonnegative
branch of finiteEtaleTateSheaf. Apply singleFunctorFlatPairing to that ordinary map;
flatness is supplied by finite_etale_torsion_twist_line. This is exactly the specified
flat-single pairing, with no choice of additional comparison data. -/
@[irreducible] def finiteAffineTatePairing
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (W : Scheme.{u}) (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w))
    (r s : ℕ) :
    ((derivedTensor (ModuleCat.{u + 1} R) W).obj
      ((DerivedCategory.singleFunctor _ 0).obj (W.finiteEtaleTateTwist N R hR r))).obj
      ((DerivedCategory.singleFunctor _ 0).obj (W.finiteEtaleTateTwist N R hR s)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj (W.finiteEtaleTateTwist N R hR (r+s)) :=
  singleFunctorFlatPairing (W.finiteEtaleTateTwist N R hR r)
    (W.finiteEtaleTateTwist N R hR s) (W.finiteEtaleTateTwist N R hR (r+s))
    ((ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line W N hN hW R hR r).2.2.1)
    (by
      have hp := ((Scheme.finiteEtaleTwistPullbackData R N hN hR).p W
        (W.toRingedSpace.isUnit_of_isUnit_germ ⊤ (N : Γ(W, ⊤))
          (fun w _ ↦ by simpa only [map_natCast] using hW w)) (r : ℤ) (s : ℤ)).hom
      simp only [← Nat.cast_add] at hp
      dsimp only [Scheme.finiteEtaleTateSheaf] at hp
      exact hp)

end AlgebraicGeometry.Etale
