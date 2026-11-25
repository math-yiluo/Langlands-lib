/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Finite-limit preservation by affine associated sheafification

Source: Stacks Project, Tag 01HV.
(blueprint: lem-sc-tilde-preserves-finite-limits). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Associated sheafification on an affine scheme preserves all finite limits.

Source: Stacks Project, Tag 01HV, exactness of associated sheafification.
(blueprint: lem-sc-tilde-preserves-finite-limits).

Proof: A kernel of a morphism between associated sheaves is quasi-coherent, so
its affine counit is invertible. Lift its kernel inclusion using full faithfulness
of tilde. The lifted kernel fork maps to a limit fork, and full faithfulness
reflects that limit. This proves preservation of kernels for every morphism.
Tilde is additive, and an additive functor between abelian categories preserving
kernels preserves finite limits. This holds for every commutative ring, including
the zero ring, and for zero morphisms and zero modules. -/
theorem tilde_preserves_finite_limits (A : Type u) [CommRing A] :
    Limits.PreservesFiniteLimits (tilde.functor (.of A)) := by
  have h : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N),
      Limits.PreservesLimit (Limits.parallelPair f 0) (tilde.functor (.of A)) := by
    intro M N f
    let T := tilde.functor (.of A)
    let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
    let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
    have : (T.obj M).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) M).IsQuasicoherent
      infer_instance
    have : (T.obj N).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) N).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map f)
    have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
    let e : T.obj ((moduleSpecΓFunctor (R := .of A)).obj k) ≅ k :=
      asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)
    let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
    have ht : t ≫ f = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
    let c := Limits.KernelFork.ofι t ht
    have hc : Limits.IsLimit (c.map T) := by
      apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
      exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
    have hc' : Limits.IsLimit c :=
      Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact Limits.preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  let : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N),
      Limits.PreservesLimit (Limits.parallelPair f 0) (tilde.functor (.of A)) := h
  let : (tilde.functor (.of A)).IsLeftAdjoint :=
    (tilde.adjunction (R := .of A)).isLeftAdjoint
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tilde.functor (.of A))
  let : (tilde.functor (.of A)).Additive :=
    Functor.additive_of_preservesBinaryBiproducts (tilde.functor (.of A))
  exact Functor.preservesFiniteLimits_of_preservesKernels (tilde.functor (.of A))

end AlgebraicGeometry
