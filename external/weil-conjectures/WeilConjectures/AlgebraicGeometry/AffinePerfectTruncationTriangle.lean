/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineLiftEventualFreeKernels
import WeilConjectures.AlgebraicGeometry.FiniteFreeStupidTailPerfect
import WeilConjectures.AlgebraicGeometry.ExactFunctorStupidTailTriangle

/-! # Arbitrarily low perfect truncation triangles on affine schemes

Source: Stacks Project, Tag 08EG, proof of Lemma 36.13.6, finite-free lift and truncation
(blueprint: lem-sc-affine-perfect-low-truncation-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- There are arbitrarily low finite locally free truncation triangles with a perfect
middle term extending to the ambient affine scheme. No vanishing or splitting is asserted.
Source: Stacks Project, Tag 08EG, proof of Lemma 36.13.6, first part
(blueprint: lem-sc-affine-perfect-low-truncation-triangle).

Proof:
1. Perfectness implies locally finite Tor dimension. A finite cover of the
quasi-compact open gives a common Tor interval [a,b]. Use the equivalence
X = Spec Gamma(X) to view the supplied bounded-above finite-free sheaf complex K
as a module complex P: take sections termwise, using that finite-free sheaves
are quasi-coherent and the affine tilde/sections equivalence is exact.
The resulting module complex is bounded above and termwise finite free;
its associated sheaf complex recovers K, so its restriction represents F.
2. Set N = a-1. For each r <= N, take the image K of P^(r-1) -> P^r.
On U, exactness in degree r identifies K with the next kernel. The affine
truncation-kernel finite-local-freeness theorem makes M = K|U finite locally free.
The complex Q with M in degree r-1 followed by P^r|U, P^(r+1)|U, ... represents F.
3. The tail P^r -> P^(r+1) -> ... on X is bounded finite free, hence perfect.
The degreewise short exact sequence tail|U -> Q -> M[1-r] gives a distinguished
triangle. Inverse rotation gives M[-r] -> tail|U -> F -> M[1-r]. Identify M[-r]
with the single complex in degree r. This supplies the three morphisms and the
asserted distinguished triangle for every r <= N.
The empty open and zero complex require no exception: all constructions then
restrict to zero, and the same short exact sequence gives the zero triangle.
-/
theorem exists_low_perfect_truncation_triangle
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (K.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r))))
    (hrep : Nonempty
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅ F)) :
    ∃ N : ℤ, ∀ r : ℤ, r ≤ N →
      ∃ M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
        M.IsFiniteLocallyFree ∧ ∃ P : schemeDerivedCategory X, IsPerfect X P ∧
          ∃ (i : (DerivedCategory.singleFunctor _ r).obj M ⟶
              ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                  (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                  (Modules.overEquiv U)).mapDerivedCategory.obj P)
            (p : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                  (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                  (Modules.overEquiv U)).mapDerivedCategory.obj P ⟶ F)
            (δ : F ⟶ ((DerivedCategory.singleFunctor _ r).obj M)⟦(1 : ℤ)⟧),
            Triangle.mk i p δ ∈ distTriang (schemeDerivedCategory U.toScheme) := by
  classical
  let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)
  obtain ⟨N, hN⟩ := affine_lift_eventual_free_kernels X U hU F hF K hbounded hfree hrep
  refine ⟨N, ?_⟩
  intro r hr
  obtain ⟨hexact, hM⟩ := hN r hr
  let M := kernel (R.map (K.d r (r + 1)))
  let P := DerivedCategory.Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntGE r))
  have hP : IsPerfect X P := finiteFree_stupidTail_isPerfect X K hbounded hfree r
  obtain ⟨i, p, δ, ht⟩ := DerivedCategory.exactFunctor_stupidTail_triangle R K r hexact
  obtain ⟨e⟩ := hrep
  refine ⟨M, hM, P, hP, i, p ≫ e.hom, e.inv ≫ δ, ?_⟩
  apply isomorphic_distinguished _ ht _
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_
  · simp
  · simp
  · simp


end AlgebraicGeometry.Scheme
