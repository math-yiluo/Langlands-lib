# Iterated Frobenius powers and coefficient maps

Module `Langlands.GroupScheme.Torus.FrobeniusTensorPower`, namespace
`Langlands.GroupScheme.CocharacterDescent`. It imports only Mathlib.

Throughout, `k` (or `F`) is a field of exponential characteristic `p`
(`ExpChar k p`: `p` is the characteristic if it is positive and `1` in
characteristic zero), `e` is a natural number, and `q = p ^ e`. For a
commutative ring `R` and an additive monoid `Λ`, `R[Λ]` is Mathlib's
`AddMonoidAlgebra R Λ`. For an algebra map `f`, `AddMonoidAlgebra.mapAlgHom Λ f`
applies `f` to every coefficient.

## Statements

- `add_pow_expChar_pow_of_algebra`. In every commutative `k`-algebra `R`,
  `(x + y) ^ q = x ^ q + y ^ q`.
- `pow_eq_pow_map_add`, `pow_eq_pow_map_zero`. For an additive map
  `f : R →+ R` of a commutative `k`-algebra, the set of `x` with
  `x ^ q = f x ^ q` contains `0` and is closed under addition.
- `pow_eq_pow_tensorProductMap`. Let `K` and `A` be commutative `k`-algebras
  and `g : A →ₐ[k] A` with `a ^ q = g a ^ q` for all `a : A`. Then every
  `x : K ⊗[k] A` satisfies
  `x ^ q = (Algebra.TensorProduct.map (AlgHom.id K K) g x) ^ q`.
- `pow_eq_pow_includeRight_lmul'`. Let `L` be a commutative `F`-algebra such
  that `ℓ ^ q` lies in the range of `algebraMap F L` for every `ℓ : L`. Let
  `μ = includeRight ∘ lmul' F : L ⊗[F] L →ₐ[F] L ⊗[F] L`, so
  `μ (x ⊗ y) = 1 ⊗ x y`. Then `r ^ q = μ r ^ q` for every `r : L ⊗[F] L`.
- `pow_eq_pow_mapAlgHom`. Let `R` be a commutative `k`-algebra, `Λ` a
  commutative additive monoid, and `f : R →ₐ[k] R` with `r ^ q = f r ^ q` for
  all `r : R`. Then `a ^ q = (mapAlgHom Λ f a) ^ q` for every `a : R[Λ]`.
- `pow_eq_pow_mapAlgHom_includeRight_lmul'`. Under the hypothesis on `L` above,
  `a ^ q = (mapAlgHom Λ μ a) ^ q` for every `a : (L ⊗[F] L)[Λ]`.

The requested forms had `K`, `L` fields and `Λ` an additive commutative group.
The Lean statements assume only commutative rings and a commutative additive
monoid, so they apply in that case unchanged.

## Proofs

1. Additivity. If `R` is the zero ring, both sides are equal. Otherwise
   `algebraMap k R` is injective because `k` is a field, so `R` has exponential
   characteristic `p` (Mathlib's `expChar_of_injective_algebraMap`), and
   Mathlib's `add_pow_expChar_pow` applies.
2. Closure under `0` and sums. `f 0 = 0`. If `x` and `y` are in the set, then
   by step 1 `(x + y) ^ q = x ^ q + y ^ q = f x ^ q + f y ^ q = (f x + f y) ^ q`,
   which is `f (x + y) ^ q`.
3. `pow_eq_pow_tensorProductMap`. Induction on tensors. On `a ⊗ b`,
   `(a ⊗ b) ^ q = a ^ q ⊗ b ^ q` and the image is `a ⊗ g b`, whose `q`-th power
   is `a ^ q ⊗ (g b) ^ q`, which equals `a ^ q ⊗ b ^ q` by the hypothesis on `g`.
   Sums are handled by step 2.
4. `pow_eq_pow_includeRight_lmul'`. Induction on tensors. On `x ⊗ y`, choose
   `c : F` with `x ^ q = c • 1`. Then `(x ⊗ y) ^ q = (c • 1) ⊗ y ^ q` and
   `(1 ⊗ x y) ^ q = 1 ⊗ (c • 1) y ^ q = 1 ⊗ c • y ^ q`. These are equal because
   scalars move across `⊗` (`TensorProduct.smul_tmul`). Sums are handled by
   step 2.
5. `pow_eq_pow_mapAlgHom`. Induction over `R[Λ]` (zero, sums, monomials). For
   a monomial, `(single γ r) ^ q = single (q • γ) (r ^ q)`, the image is
   `single γ (f r)`, and its `q`-th power is `single (q • γ) (f r ^ q)`. These
   agree by the hypothesis on `f`. Zero and sums are handled by step 2, since
   `R[Λ]` is a commutative `k`-algebra.
6. The last statement is step 5 applied to `μ`, with the hypothesis from step 4.

## Provenance

These are elementary facts about the Frobenius map, which is additive in
characteristic `p`. They are derived internal helpers, not quoted from a
source. They were requested by Worker 1001 for the purely inseparable step of
torus cocharacter detection. That step descends a cocharacter datum along a
purely inseparable extension `L / F` of exponent `e`, using that `μ` agrees
with the identity after taking `q`-th powers. That application is in a
separate module; this module states only the algebraic identities above.
