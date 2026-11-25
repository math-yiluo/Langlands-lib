/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-! # Scalar extension along equal coefficient maps
Source: Stacks Project, Tag 05G3, tensor associativity and scalar extension.
(blueprint: lem-pc-base-localization-dlinear-glue). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat
private theorem extendScalars_eqToIso_one_tmul
    {E F : Type u} [CommRing E] [CommRing F] (f g : E →+* F) (h : f = g)
    (M : ModuleCat.{u} E) (x : M) :
    (eqToIso (congrArg (fun k : E →+* F ↦ (ModuleCat.extendScalars k).obj M) h)).hom
        ((1 : F) ⊗ₜ[E,f] x) = (1 : F) ⊗ₜ[E,g] x := by
  subst g
  rfl
/-- Transport an invertible semilinear map through a coefficient-ring isomorphism.
Source: Stacks Project, Tag 05G3, tensor associativity.
(blueprint: lem-pc-base-localization-dlinear-glue).

Proof: the ring isomorphism makes restriction of scalars an equivalence, so
its scalar-extension counit is invertible. Extend g and compose with that
counit to obtain an F-linear isomorphism from F tensor_E M to N. Extend this
isomorphism along q to D. Tensor associativity identifies its source with
D tensor_E M, since q composed with phi equals p. On 1 tensor x, the
associator gives 1 tensor (1 tensor x), the extension of g gives
1 tensor (1 tensor g(x)), and the counit gives 1 tensor g(x).
This uses no flatness of D and applies to zero rings and zero modules. -/
theorem exists_extendScalars_iso_of_ringEquiv
    {E F D : Type u} [CommRing E] [CommRing F] [CommRing D]
    (φ : E ≃+* F) (p : E →+* D) (q : F →+* D) (h : q.comp φ.toRingHom = p)
    (M : ModuleCat.{u} E) (N : ModuleCat.{u} F)
    (g : M ⟶ (restrictScalars φ.toRingHom).obj N) (hg : IsIso g) :
    ∃ e : (extendScalars p).obj M ≅ (extendScalars q).obj N,
      ∀ x : M, e.hom ((1 : D) ⊗ₜ[E,p] x) = (1 : D) ⊗ₜ[F,q] g x := by
  let := hg
  let adj := extendRestrictScalarsAdj φ.toRingHom
  let e₀ : (extendScalars φ.toRingHom).obj M ≅ N :=
    (extendScalars φ.toRingHom).mapIso (asIso g) ≪≫ asIso (adj.counit.app N)
  have he₀ (x : M) : e₀.hom ((1 : F) ⊗ₜ[E,φ.toRingHom] x) = g x := by
    change adj.counit.app N ((extendScalars φ.toRingHom).map g
      ((1 : F) ⊗ₜ[E,φ.toRingHom] x)) = _
    rw [ExtendScalars.map_tmul]
    exact extendRestrictScalarsAdj_counit_app_apply_one_tmul _ N (g x)
  let T := extendScalars q
  let ι := (extendScalarsComp φ.toRingHom q).app M
  have heq := congrArg (fun k : E →+* D ↦ (extendScalars k).obj M) h.symm
  refine ⟨eqToIso heq ≪≫ ι ≪≫ T.mapIso e₀, ?_⟩
  intro x
  change T.map e₀.hom (ι.hom ((eqToIso heq).hom ((1 : D) ⊗ₜ[E,p] x))) = _
  rw [extendScalars_eqToIso_one_tmul _ _ h.symm]
  have hι : ι.hom ((1 : D) ⊗ₜ[E,q.comp φ.toRingHom] x) =
      (1 : D) ⊗ₜ[F,q] ((1 : F) ⊗ₜ[E,φ.toRingHom] x) :=
    extendScalarsComp_hom_app_one_tmul φ.toRingHom q M x
  rw [hι]
  have hmap := ExtendScalars.map_tmul q e₀.hom (1 : D)
    ((1 : F) ⊗ₜ[E,φ.toRingHom] x)
  change T.map e₀.hom ((1 : D) ⊗ₜ[F,q] ((1 : F) ⊗ₜ[E,φ.toRingHom] x)) = _
  rw [hmap]
  exact congrArg (fun y ↦ (1 : D) ⊗ₜ[F,q] y) (he₀ x)
end ModuleCat
