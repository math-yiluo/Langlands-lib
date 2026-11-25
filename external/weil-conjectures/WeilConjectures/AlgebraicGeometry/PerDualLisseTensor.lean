/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Dual of a lisse tensor

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/lem-per-dual-lisse-tensor.md`
(blueprint: lem-per-dual-lisse-tensor).

The statement is formulated in the closed symmetric monoidal category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of bounded
constructible complexes, with the Verdier dual `𝔻_X K = RHom(K, ω_X)` of
`ProEtale.CondensedRing.verdierDual`. The dual `L^∨` of `L` is its internal Hom `RHom(L, ℚ̄_ℓ)`
into the unit; for `L` a lisse module placed in degree zero, this is the linear dual.

## Main definitions

- `ProEtale.CondensedRing.verdierDualTensorComparison`: the canonical map
  `𝔻_X K ⊗ᴸ L^∨ ⟶ 𝔻_X (K ⊗ᴸ L)`, the transpose of the product of the two evaluation pairings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The canonical comparison map `𝔻_X K ⊗ᴸ L^∨ ⟶ 𝔻_X (K ⊗ᴸ L)`, for `L^∨ = RHom(L, ℚ̄_ℓ)`: the
transpose of the pairing
```
(K ⊗ᴸ L) ⊗ᴸ (𝔻_X K ⊗ᴸ L^∨) ⟶ (K ⊗ᴸ 𝔻_X K) ⊗ᴸ (L ⊗ᴸ L^∨) ⟶ ω_X ⊗ᴸ ℚ̄_ℓ ≅ ω_X
```
given by the middle interchange (`tensorμ`) followed by the two evaluation maps. -/
noncomputable def verdierDualTensorComparison {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    verdierDual ℓ K ⊗ (ihom L).obj (𝟙_ _) ⟶ verdierDual ℓ (K ⊗ L) :=
  curry (tensorμ K L (verdierDual ℓ K) ((ihom L).obj (𝟙_ _)) ≫
    ((ihom.ev K).app (dualizingComplex ℓ X) ⊗ₘ (ihom.ev L).app (𝟙_ _)) ≫
    (ρ_ (dualizingComplex ℓ X)).hom)

/-- The Verdier dual of a bounded constructible complex tensored with a lisse module is
canonically the tensor of its Verdier dual with the dual module: the canonical map
`verdierDualTensorComparison : 𝔻_X K ⊗ᴸ L^∨ ⟶ 𝔻_X (K ⊗ᴸ L)` is an isomorphism, for `L` a lisse
module `M` placed in degree zero.

(blueprint: lem-per-dual-lisse-tensor)
Source: latest blueprint, `part-weights-riemann-hypothesis/sec-fourier-transform/`
`sec-wft-perverse/sk-lem-wft-curve-heart/lem-per-dual-lisse-tensor.md` and its proof
(`lem-per-dual-lisse-tensor.proof.md`), paragraphs 1--3.

Proof (the four DAG steps):
1. Work in the ordinary uncompleted derived category over the pulled-back condensed
   coefficient ring. The module-object/ringed-site comparison preserves tensor, internal
   Hom, evaluation and restriction. Tensor--Hom currying gives
   `RHom(K ⊗ᴸ L, omega) ≅ RHom(K, RHom(L, omega))`.
2. On a pro-etale cover trivializing `L` as a finite free module, strict-perfect Hom
   identifies `RHom(L, omega)` with the corresponding finite power of `omega`.
   The ordinary-to-derived dual map is locally the identity, and the evaluation map
   `L`'s ordinary dual tensored with `omega` to `RHom(L, omega)` is locally the
   finite-free coordinate isomorphism. Hom restriction and tensor pullback preserve it.
3. Put `V = Hom(L, B)`. Transpose evaluation, using symmetry, to obtain
   `beta : RHom(K, omega) ⊗ᴸ V → RHom(K, V ⊗ᴸ omega)`. On a trivializing slice
   both sides are the same finite power of `RHom(K, omega)` and `beta` is the identity.
   This uses finite products and adjunction and requires no perfectness of `K`.
4. Exact restriction commutes with cohomology. The comparison cones vanish on the cover,
   so sheaf descent makes them vanish globally. Invert the first comparison inside
   `RHom(K, -)` and invert `beta`; their composition with currying is the asserted
   canonical isomorphism. This is compatible with all slice restrictions.
-/
theorem per_dual_lisse_tensor {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) M)
    (e : L.obj ≅ (DerivedCategory.singleFunctor _ 0).obj M) :
    IsIso (verdierDualTensorComparison ℓ K L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
