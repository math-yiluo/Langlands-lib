# Completion of a quotient of a Noetherian local ring

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` compares the
maximal-ideal adic completions of a Noetherian local ring `A` and of a local
ring `A'` that is a quotient of `A`. Write `Â` for
`AdicCompletion (maximalIdeal A) A` and `Â'` for
`AdicCompletion (maximalIdeal A') A'`. All declarations are in the namespace
`Langlands.CommutativeAlgebra.FiniteTypeIntGRing`, and all universes are
arbitrary.

## Statements

- `isAdicComplete_map_algebraMap_of_algEquiv`: let `R` be a commutative ring,
  `S` and `S'` commutative `R`-algebras, `e : S ≃ₐ[R] S'` and `I` an ideal of
  `R`. If `S` is adically complete for the extended ideal `I S`, then `S'` is
  adically complete for `I S'`.
- `isAdicComplete_tensor_adicCompletion`: let `A` be a Noetherian local ring
  and `A'` a commutative `A`-algebra that is finite as an `A`-module. Then the
  ring `A' ⊗[A] Â` is adically complete for the extended ideal
  `(maximalIdeal A) (A' ⊗[A] Â)`.
- `nonempty_adicCompletion_algEquiv_tensor`: let `A` be a Noetherian local
  ring, `A'` a local ring and `A'` an `A`-algebra whose structure map
  `algebraMap A A'` is surjective. Then there is an `A'`-algebra isomorphism
  `Â' ≃ₐ[A'] A' ⊗[A] Â`.
- `tensorAdicCompletionEquivOfSurjective h K`: under the hypotheses of the
  previous item (`h` is the surjectivity of `algebraMap A A'`), for every
  commutative ring `K` with compatible algebra structures over `A` and `A'`
  (`IsScalarTower A A' K`), a ring isomorphism
  `K ⊗[A] Â ≃+* K ⊗[A'] Â'`.

`A'` is not assumed Noetherian; that follows from the surjectivity of
`A → A'`. The third statement is the standard fact that for an ideal `I` of a
Noetherian local ring `A`, the completion of `A/I` is `A/I ⊗_A Â`. The fourth
is the form used in the proof of the G-ring property, where `K` is a residue
field of a prime of `A'`: it identifies the fibre of `A' → Â'` over that prime
with the fibre of `A → Â` over the corresponding prime of `A`. This module is
internal to the project's proof and does not follow a specific reference.

## Proofs

**Transport of completeness.** Mathlib's `IsAdicComplete.congr_ringEquiv`
transports completeness along the ring isomorphism underlying `e`, for the
image of `I S` under `e`. That image is `I S'` because `e` commutes with the
structure maps from `R`.

**Completeness of `A' ⊗[A] Â`.** The completion `Â` is Noetherian by
`AdicCompletion.isNoetherianRing_of_isNoetherianRing` (imported from
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing`),
and Mathlib provides that `Â` is a local ring complete for its maximal ideal.
The module `Â ⊗[A] A'` is finite over `Â`, so it is complete for the maximal
ideal of `Â` by `IsAdicComplete.of_finite_of_isNoetherianRing` (imported from
`Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing`).
Mathlib's `AdicCompletion.maximalIdeal_eq_map` says that this maximal ideal is
`(maximalIdeal A) Â`. Mathlib's `IsAdicComplete.map_algebraMap_iff`, applied
twice, turns this first into completeness of `Â ⊗[A] A'` as an `A`-module for
`maximalIdeal A`, and then into completeness as a ring for the extended ideal
`(maximalIdeal A) (Â ⊗[A] A')`. The commutativity isomorphism
`Algebra.TensorProduct.comm A Â A'` and the first statement give the result.

**The isomorphism `Â' ≅ A' ⊗[A] Â`.** Put `T = A' ⊗[A] Â` and
`J = (maximalIdeal A') T`. Mathlib's `IsLocalRing.map_maximalIdeal_of_surjective`
gives `(maximalIdeal A) A' = maximalIdeal A'`, so `J = (maximalIdeal A) T`.
Surjectivity makes `A'` a finite `A`-module, so `T` is `J`-adically complete
by the second statement. The proof applies the imported criterion
`AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow`
(module
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow`)
to `algebraMap A' T`. It checks, for every `k`, that the composite
`A' → T → T ⧸ J ^ k` is surjective with kernel `maximalIdeal A' ^ k`.

- *Surjectivity.* Write elements of `T` as sums of pure tensors and treat one
  pure tensor `a' ⊗ x` at a time. By `AdicCompletion.exists_eq_algebraMap_add`
  (from `Langlands.AnthropicFLT.Definitions.Def_AdicCompletionLocalRing`),
  `x = a + z`, where `a` is the image of an element of `A` and
  `z ∈ (maximalIdeal A ^ k) Â`. Then `1 ⊗ z ∈ J ^ k`, and
  `a' ⊗ x - (a' · a) ⊗ 1 = (a' ⊗ 1)(1 ⊗ z)` lies in `J ^ k`. So `a' ⊗ x` is
  congruent modulo `J ^ k` to the image of `a' · a ∈ A'`. Sums are handled by
  additivity.
- *Kernel.* The kernel contains `maximalIdeal A' ^ k` because
  `J ^ k = (maximalIdeal A' ^ k) T`. For the other inclusion, let `ψ` be the
  `A`-algebra map `Â → A ⧸ maximalIdeal A ^ k → A' ⧸ maximalIdeal A' ^ k`
  given by evaluation at level `k` (`AdicCompletion.evalₐ`) followed by the map
  induced by `A → A'` (`Ideal.quotientMapₐ`). Then
  `Algebra.TensorProduct.lift` builds the `A'`-algebra map
  `ρ : T → A' ⧸ maximalIdeal A' ^ k` with `ρ (a' ⊗ x) = a' · ψ x`. Being
  `A'`-linear, `ρ` vanishes on `(maximalIdeal A' ^ k) T = J ^ k`. If `a'` lies
  in the kernel, then `algebraMap A' T a' ∈ J ^ k`, so the class of `a'` in
  `A' ⧸ maximalIdeal A' ^ k`, which is `ρ (algebraMap A' T a')`, is zero.

The criterion gives a ring isomorphism `Â' ≃+* AdicCompletion J T` that sends
the image of each `r ∈ A'` to the image of `algebraMap A' T r`. Since `T` is
`J`-adically complete, composing with the inverse of Mathlib's
`AdicCompletion.ofAlgEquiv J` gives a ring isomorphism `Â' ≃+* T` that commutes
with the maps from `A'`. `AlgEquiv.ofRingEquiv` makes it an `A'`-algebra
isomorphism.

**Base change.** Choose an isomorphism `E : Â' ≃ₐ[A'] A' ⊗[A] Â` from the third
statement. Mathlib's `Algebra.TensorProduct.cancelBaseChange A A' A' K Â` is an
isomorphism `K ⊗[A'] (A' ⊗[A] Â) ≃ₐ[A'] K ⊗[A] Â`. The required ring
isomorphism is its inverse followed by `Algebra.TensorProduct.congr` of the
identity of `K` and `E.symm`.
