/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelComplex
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelBounded
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelRetracts

/-! # Strict perfectness of the explicit affine finite free model

Source: Stacks Project, Tag 068C and Definition 08C4
(blueprint: lem-affine-finite-free-perfect-core).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The explicitly sheafified and extended bounded finite free complex is strictly perfect.
Source: Stacks Project, Tag 068C, affine finite free resolution argument, and Definition 08C4
(blueprint: lem-affine-finite-free-perfect-core).

Proof: In degree `-n`, the extension is canonically isomorphic to the sheafification
of `K.X n`; in positive degrees its terms are zero. A finite free module admits a
finite basis, which identifies it with the finitely supported functions on that
basis. Apply `tildeFinsupp` to identify its associated sheaf with a finite free
structure-sheaf module. Restriction along the affine-chart isomorphism and the
inverse open-site equivalence preserve the unit sheaf and coproducts, hence
preserve these finite free modules. Reindex the finite basis by `ULift (Fin m)`.
The resulting isomorphism gives the required inclusion and projection with
identity composite. For positive degrees use the empty basis. For degrees below
`-r`, the input term is zero by `hzero`, and the additive transport preserves zero
objects. The bounds are `-r` and `0`. This also treats the zero ring, the empty
open, zero-rank terms, and `r = 0`: no basis is required to have positive rank. -/
theorem affine_finite_free_perfect_core {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) (r : ℕ)
    (hfree : ∀ n, Module.Free (Γ(Y, U) : Type u) (K.X n))
    (hfinite : ∀ n, Module.Finite (Γ(Y, U) : Type u) (K.X n))
    (hzero : ∀ n, r < n → IsZero (K.X n)) :
    Scheme.IsStrictlyPerfect Y U (affineFiniteFreeModelComplex U hU K) := by
  refine ⟨affine_finite_free_model_bounded U hU K r hzero, ?_⟩
  exact affine_finite_free_model_retracts U hU K hfree hfinite

end AlgebraicGeometry
