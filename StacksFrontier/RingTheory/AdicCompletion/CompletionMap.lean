module

public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The completion of an algebra map

For an `A`-algebra `B` and an ideal `I` of `A`, `AdicCompletion.completionMap I` is the induced
algebra map from the `I`-adic completion of `A` to the `IB`-adic completion of `B`. For a ring
homomorphism `f : A →+* B` carrying an ideal `J` of `A` into an ideal `I` of `B`,
`adicCompletionMap f J I` is the induced ring homomorphism from the `J`-adic completion of `A` to
the `I`-adic completion of `B`.

## Main definitions

* `AdicCompletion.completionMap`: the algebra map `A^∧_I → B^∧_{IB}` induced by `A → B`.
* `adicCompletionMap`: the ring homomorphism `A^∧_J → B^∧_I` induced by `f : A →+* B` with
  `J.map f ≤ I`.
-/

@[expose] public section

universe u v

namespace AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The level-`n` map `AdicCompletion I A → B ⧸ (IB) ^ n`, the level-`n` evaluation followed by
the reduction of `A → B`. -/
noncomputable def completionLevel (I : Ideal A) (n : ℕ) :
    AdicCompletion I A →ₐ[A] B ⧸ (I.map (algebraMap A B)) ^ n :=
  (Ideal.quotientMapₐ ((I.map (algebraMap A B)) ^ n) (Algebra.ofId A B)
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)).comp (evalₐ I n)

/-- The level maps `completionLevel` are compatible with the transition maps. -/
theorem factor_completionLevel (I : Ideal A) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
        (completionLevel (B := B) I n) = completionLevel I m := by
  ext x
  simp only [completionLevel, AlgHom.coe_comp, Function.comp_apply]
  rw [← stacks_factorPow_evalₐ I hmn x]
  exact congr($(Ideal.Quotient.factorPow_comp_quotientMap (algebraMap A B) I
    (I.map (algebraMap A B)) hmn (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)) (evalₐ I n x))

/-- The completion of an algebra map, as an algebra map from the `I`-adic completion of the base
to the completion of the algebra along the extended ideal. -/
noncomputable def completionMap (I : Ideal A) :
    AdicCompletion I A →ₐ[A] AdicCompletion (I.map (algebraMap A B)) B :=
  liftAlgHom _ (completionLevel I) (fun hmn => factor_completionLevel I hmn)

/-- Level-`n` evaluation of `completionMap` sends a representative `a` of `x` to the class of
`algebraMap A B a`. -/
theorem evalₐ_completionMap (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) (a : A)
    (ha : evalₐ I n x = Ideal.Quotient.mk (I ^ n) a) :
    evalₐ (I.map (algebraMap A B)) n (completionMap (B := B) I x) =
      Ideal.Quotient.mk _ (algebraMap A B a) := by
  rw [completionMap, evalₐ_liftAlgHom _ (completionLevel I)
    (fun hmn => factor_completionLevel I hmn)]
  simp [completionLevel, ha]

/-- Level-`n` value of `completionMap`: it sends a representative `a` of `x` at level `n` to the
class of `algebraMap A B a`. -/
theorem val_completionMap (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) (a : A)
    (ha : x.val n = Submodule.Quotient.mk a) :
    (completionMap (B := B) I x).val n = Submodule.Quotient.mk (algebraMap A B a) :=
  val_eq_mk _ n _ _ (evalₐ_completionMap I n x a (evalₐ_eq_mk I n x a ha))

end AdicCompletion

/-! ### The induced map for an arbitrary ring homomorphism -/
