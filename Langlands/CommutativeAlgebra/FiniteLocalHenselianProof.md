# Proof: finite local algebras over Henselian local rings are Henselian

This module proves `Langlands.CommutativeAlgebra.FiniteLocalHenselianStatement.{u,v}` as
`Langlands.CommutativeAlgebra.finiteLocalHenselian`. The carrier universes are `u` for the
Henselian base ring `R` and `v` for the local algebra `S`.

```lean
theorem finiteLocalHenselian : FiniteLocalHenselianStatement.{u, v}
```

## Statement proved

Let `R` be a Henselian local ring and let `S` be a commutative local ring with an
`R`-algebra structure that makes `S` a finite `R`-module. Then `S` is Henselian
(`HenselianLocalRing S`). Concretely: if `f ∈ S[X]` is monic, `a₀ ∈ S`, `f(a₀) ∈ 𝔪_S` and
`f'(a₀)` is a unit, then some `a ∈ S` satisfies `f(a) = 0` and `a - a₀ ∈ 𝔪_S`. No Noetherian,
flatness or residue-field hypothesis is used.

## Proof

The module works in the namespace `Langlands.CommutativeAlgebra.FiniteLocalHenselian` and has
four steps.

1. **Lifting idempotents modulo `𝔪_R A`, in any universe.**
   `exists_isIdempotentElem_sub_mem_map_maximalIdeal` takes a module-finite `R`-algebra `A` in an
   arbitrary universe and `x ∈ A` with `x² - x ∈ 𝔪_R A`. It returns an idempotent `e ∈ A` with
   `e - x ∈ 𝔪_R A`. The Library lemma `henselian_lift_single_idem` in
   `StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ProductOfLocalRings` gives this for
   algebras in the universe `max u v`. The proof applies it to `ULift.{u} A` and transports the
   result back along `ULift.algEquiv`. The ideal `𝔪_R A` corresponds to `𝔪_R (ULift A)` under
   `Ideal.map_map`.

2. **Lifting idempotents modulo `𝔪_S A`.** Let `S` be local and module-finite over `R`, and let
   `A` be module-finite over `S`, with a compatible `R`-algebra structure.
   - By `maximalIdeal_le_radical_map_maximalIdeal`, `𝔪_S` lies in the radical of `𝔪_R S`. Let
     `P` be a prime of `S` that contains `𝔪_R S`. Its contraction to `R` contains `𝔪_R`, so it
     equals `𝔪_R`. Then `P` is maximal, by integrality
     (`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`), so `P = 𝔪_S`.
   - `𝔪_R S ≤ 𝔪_S`, because the contraction of `𝔪_S` is maximal
     (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`). With `Ideal.map_radical_le` this gives
     `𝔪_R A ≤ 𝔪_S A ≤ rad(𝔪_R A)`.
   - So the factor map `A/𝔪_R A → A/𝔪_S A` has nil kernel. By
     `exists_isIdempotentElem_eq_of_ker_isNilpotent`, an idempotent of `A/𝔪_S A` lifts to an
     idempotent of `A/𝔪_R A`. Step 1 lifts that to `A`.

   This is `exists_isIdempotentElem_sub_mem_map_maximalIdeal_of_finite`.

3. **An approximate idempotent for the simple root.** In `exists_isRoot_sub_mem_maximalIdeal`,
   put `A = AdjoinRoot f` and `x = root f`. `A` is finite over `S` by
   `Polynomial.Monic.finite_adjoinRoot`.
   - Division by `X - a₀` (`modByMonic_X_sub_C_eq_C_eval`, `modByMonic_add_div`) gives
     `f = f(a₀) + (X - a₀) g` and `g = g(a₀) + (X - a₀) h`.
   - Differentiating the first identity shows `g(a₀) = f'(a₀)`, so `g(a₀)` is a unit `u`.
   - Set `ε₀ = u⁻¹ g(x)`. Then `ε₀ (x - a₀) = -u⁻¹ f(a₀) ∈ 𝔪_S A` and
     `ε₀² - ε₀ = ε₀ (x - a₀) · u⁻¹ h(x) ∈ 𝔪_S A`.
   - Step 2 gives an idempotent `e` with `e - ε₀ ∈ 𝔪_S A`. Hence `e (x - a₀) ∈ 𝔪_S A`.
   - Let `φ : A → κ(S)` be `AdjoinRoot.lift` of the residue map, sending `x ↦ a₀ mod 𝔪_S`. This
     is well defined because `f(a₀) ∈ 𝔪_S`. `φ` kills `𝔪_S A` and `φ(ε₀) = 1`, so `φ(e) = 1`.

4. **The factor `B = A ⧸ (1 - e)` is `S`.** Let `π : A → B` be the quotient map. Then
   `π(e) = 1`, so `π(x) - a₀ ∈ 𝔪_S B`.
   - *Surjectivity.* Every element of `B` is `π(p(x))` for a polynomial `p`, and
     `π(p(x)) - p(a₀) ∈ 𝔪_S B` by `sub_dvd_eval_sub`. So `⊤ ≤ S·1 ⊔ 𝔪_S • ⊤` as `S`-submodules
     of `B` (`Ideal.smul_top_eq_map`). `B` is a finite `S`-module, so Nakayama's lemma
     (`Submodule.le_of_le_smul_of_le_jacobson_bot`) shows that `S → B` is surjective. Choose `a`
     with `a = π(x)` in `B`.
   - *Injectivity.* Suppose `s ↦ 0` in `B`. Then `s = w (1 - e)` in `A`, so `s e = 0`. Use the
     coordinates of `e` in the power basis `AdjoinRoot.powerBasis'`. If all of them were in
     `𝔪_S`, then `e ∈ 𝔪_S A` and `φ(e) = 0`, which is false. So some coordinate is a unit. It is
     killed by `s`, so `s = 0`.
   - *Conclusion.* `f(a)` maps to `aeval (π x) f = π(f(x)) = 0` in `B`, so `f(a) = 0` by
     injectivity. Also `a - x ∈ (1 - e)A`, and applying `φ` gives `residue a = residue a₀`,
     that is, `a - a₀ ∈ 𝔪_S`.

Finally, `finiteLocalHenselian` packages step 4 as the field `is_henselian` of
`HenselianLocalRing S`.

## Provenance

The statement is The Stacks Project, *Commutative Algebra*, version `ed88ff78`, Section 153,
Lemma 153.4 (Tag 04GH), assertion (2), printed p.414 of the registered source
`stacks-commutative-algebra-chapter-ed88ff78`
(`Stacks Project - Commutative Algebra, full chapter PDF (version ed88ff78).pdf`, SHA-256
`b035a1f02104906a1820636cd332a0d7962fef3318d207a056634cb14dc86947`). The source deduces
assertion (2) from Lemma 153.3 (Tag 04GG): every finite `S`-algebra is a finite `R`-algebra, and
so it is a finite product of local rings (part (10)). Then the proof of (10) ⇒ (1), printed
p.413, applies to `S`. That proof takes the local factor `A₁` of `S[T]/(f)` whose closed fibre
is `κ[T]/(T - a₀)`. `A₁` is a summand of a finite free module, hence free of rank one, so
`S → A₁` is an isomorphism.

The Lean proof follows the same plan, with three differences:
- It does not decompose `S[T]/(f)` into all its local factors. It constructs only the idempotent
  `e` that cuts out `A₁`. This uses the Library's Henselian idempotent lift over `R`, which is
  the core of the Library's proof of part (10) for `R` (`exists_algEquiv_pi_isLocalRing`).
- A nil-kernel step passes from `𝔪_R` to `𝔪_S`.
- It replaces "free of rank one" by a direct Nakayama surjectivity argument and an injectivity
  argument with power-basis coordinates.

The source also concludes that `R → S` is a local ring map. The statement does not include that
conclusion, and this module does not export it. The inclusion `𝔪_R S ≤ 𝔪_S` appears only as an
intermediate step.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
