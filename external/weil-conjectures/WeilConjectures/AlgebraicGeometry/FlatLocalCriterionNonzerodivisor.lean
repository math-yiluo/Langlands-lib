/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import WeilConjectures.Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Local criterion of flatness modulo a nonzerodivisor

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00ML and the remark
following it (blueprint: lem-weil-pbc-flat-local-criterion-nonzerodivisor).
-/

@[expose] public section

universe u v w

open scoped Pointwise

namespace RingTheory

/-- Local criterion of flatness modulo a nonzerodivisor.

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00ML and the remark
following it (blueprint: lem-weil-pbc-flat-local-criterion-nonzerodivisor).

The local homomorphism `φ` is `algebraMap A B`, and `M` is an `A`-module via `φ` by the
scalar tower, so `IsSMulRegular M x` is injectivity of multiplication by `φ(x)` on `M`.
`QuotSMulTop x M` is `M / xM`, a module over `A ⧸ Ideal.span {x} = A/xA`.

Proof (the two steps of the node):
1. Put `I = (x)`. Since `x` belongs to the maximal ideal, `I` is proper. Regularity of
   `x` makes the surjective map `A → I`, `a ↦ a * x`, injective, hence an isomorphism.
   Tensoring this isomorphism with `M` and using `A ⊗[A] M ≃ M` gives an isomorphism
   `β : M ≃ I ⊗[A] M` sending `m` to `x ⊗ m`. The multiplication map
   `μ : I ⊗[A] M → M`, `a ⊗ m ↦ φ(a) • m`, composed with `β`, is multiplication
   by `φ(x)`. This is injective by hypothesis, so `μ` is injective. This is the
   remark after Tag 00ML read through Remark Tag 00M6, which identifies Tor with
   the kernel of `μ`; no Tor construction is needed here.
2. The submodule `I • M` equals `xM`, and `A/I = A/xA`, so the quotient-flatness
   hypothesis is exactly flatness of `M/IM` over `A/I`
   (`def-weil-pbc-flat-ring-map`). Apply `lem-weil-pbc-flat-variant-local-criterion`
   (Tag 00ML) to the given local homomorphism of Noetherian local rings, the proper
   ideal `I`, and the finite `B`-module `M`, using injectivity of `μ` from step 1
   and quotient flatness. It gives flatness of `M` over `A`.
-/
theorem flat_of_localCriterion_nonzerodivisor
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M]
    (x : A) (hx_mem : x ∈ IsLocalRing.maximalIdeal A)
    (hx_reg : x ∈ nonZeroDivisors A) (hxM : IsSMulRegular M x)
    (hquot : Module.Flat (A ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Flat A M := by
  classical
  have hjac : (Ideal.span {x}).map (algebraMap A B) ≤ Ideal.jacobson (⊥ : Ideal B) := by
    exact ((Ideal.map_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx_mem))).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap A B))).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hinj : Function.Injective ((Ideal.span {x}).subtype.lTensor M) := by
    -- Identify the principal ideal with A, then tensor this equivalence on the left.
    let I : Ideal A := Ideal.span {x}
    let f : A →ₗ[A] I := (LinearMap.toSpanSingleton A A x).codRestrict I
      (fun a ↦ Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
    have hf : Function.Surjective f := by
      intro a
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp a.property
      exact ⟨b, Subtype.ext hb⟩
    have hf_inj : Function.Injective f := by
      intro a b h
      exact (isRegular_iff_mem_nonZeroDivisors.mpr hx_reg).2
        (congrArg Subtype.val h)
    let e := LinearEquiv.ofBijective f ⟨hf_inj, hf⟩
    -- Under the right unitor, the composite is multiplication by x on M.
    have hcompat : ∀ t, TensorProduct.rid A M (I.subtype.lTensor M (f.lTensor M t)) =
        x • TensorProduct.rid A M t := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul m a => simp [f, LinearMap.toSpanSingleton, mul_smul, mul_comm]
      | add t s ht hs => simp [ht, hs, smul_add]
    intro t s h
    obtain ⟨t', rfl⟩ := (e.lTensor M).surjective t
    obtain ⟨s', rfl⟩ := (e.lTensor M).surjective s
    have heq := congrArg (TensorProduct.rid A M) h
    change TensorProduct.rid A M (I.subtype.lTensor M (f.lTensor M t')) =
      TensorProduct.rid A M (I.subtype.lTensor M (f.lTensor M s')) at heq
    rw [hcompat, hcompat] at heq
    exact congrArg (e.lTensor M) ((TensorProduct.rid A M).injective (hxM heq))
  have hflat : Module.Flat (A ⧸ Ideal.span {x})
      (M ⧸ (Ideal.span {x} : Ideal A) • (⊤ : Submodule A M)) := by
    have := hquot
    -- Extend the quotient equivalence to A/(x) using its surjective algebra map.
    let e := Submodule.quotEquivOfEq
      ((Ideal.span {x} : Ideal A) • (⊤ : Submodule A M))
      (x • (⊤ : Submodule A M)) (Submodule.ideal_span_singleton_smul x ⊤)
    exact Module.Flat.of_linearEquiv
      (e.extendScalarsOfSurjective (S := A ⧸ Ideal.span {x})
        (Ideal.Quotient.mk_surjective))
  exact Module.Flat.of_flat_quotient_of_lTensor_injective
    (I := Ideal.span {x}) (M := M) hjac hinj

end RingTheory
