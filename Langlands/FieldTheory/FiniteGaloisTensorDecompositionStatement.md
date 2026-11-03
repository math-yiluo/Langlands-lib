# Statement: the explicit decomposition of `L ⊗[k] L` for a finite Galois extension

Authors: Worker 928.

`Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement.{u}` is a
proposition definition, not a theorem. It states the decomposition; it does
not prove it or supply an equivalence.

## Exact statement

For every pair of fields `k L : Type u` in one arbitrary universe `u`,
with `Algebra k L`, `FiniteDimensional k L` and `IsGalois k L`, there is an
`L`-algebra equivalence

```
e : (L ⊗[k] L) ≃ₐ[L] (Gal(L/k) → L)
```

such that, for all `a b : L` and `σ : Gal(L/k)`,

```
e (a ⊗ₜ[k] b) σ = a * σ b.
```

Here `Gal(L/k)` is Mathlib's notation for the group `L ≃ₐ[k] L` of
`k`-algebra automorphisms of `L`. `σ b` is `σ` applied to `b`. `a ⊗ₜ[k] b`
is the pure tensor in Mathlib's algebra tensor product `L ⊗[k] L`. The fields,
the algebra structure and both hypotheses are quantified inside the
proposition, so its only parameter is the universe level. There is no
characteristic restriction, perfectness hypothesis or other extra assumption.
The equivalence is part of the conclusion. The statement does not take a
normal basis, primitive element, algebraic closure, bijectivity certificate
or chosen decomposition as input.

## Factor and algebra conventions

- **Source.** `L ⊗[k] L` is an `L`-algebra through its **first** tensor
  factor. This is Mathlib's default instance
  `Algebra.TensorProduct.leftAlgebra`, so
  `algebraMap L (L ⊗[k] L) c = c ⊗ₜ 1` and `c • (a ⊗ₜ b) = (c * a) ⊗ₜ b`.
  The right-factor structure `Algebra.TensorProduct.rightAlgebra` is an
  `abbrev`, not a global instance, so it is not used.
- **Target.** `Gal(L/k) → L` is a product of copies of `L` indexed by the Galois
  group. It has the pointwise ring operations and the instance `Pi.algebra`,
  whose structure map sends `c` to the constant function `fun _ => c`.
- **The two structure maps.** Since `σ 1 = 1` and `1 * x = x`, the formula
  gives:
  - `e (a ⊗ₜ 1) = fun _ => a`. The first coordinate map `a ↦ a ⊗ₜ 1`
    becomes the diagonal (constant) embedding of `L`. That is the algebra
    map of the target, consistent with `e` being `L`-linear.
  - `e (1 ⊗ₜ b) = fun σ => σ b`. The second coordinate map `b ↦ 1 ⊗ₜ b`
    becomes the map whose `σ`-component is the automorphism `σ`.

  So on the factor indexed by `σ`, the two coordinate maps `L → L ⊗[k] L`
  become `id` and `σ`. A consumer can read off both maps by applying the
  formula with `b = 1` or `a = 1`.
- **Uniqueness.** Pure tensors generate `L ⊗[k] L` additively, so at most one
  additive map satisfies the formula. Any two witnesses `e` are therefore
  equal. The statement fixes the decomposition and both structure maps
  exactly, not merely up to isomorphism.

## Mathematical rationale (derived content)

What follows explains why the proposition is true. It is not a Lean proof,
and no proof is supplied with this statement.

1. *The map exists.* Fix `σ`. The map `(a, b) ↦ a * σ b` is `k`-bilinear,
   because `σ` is `k`-linear. So `a ⊗ b ↦ (σ ↦ a * σ b)` defines a map
   `L ⊗[k] L → (Gal(L/k) → L)`. It is multiplicative because each `σ` is a
   ring homomorphism, it sends `1 ⊗ 1` to `1`, and it is `L`-linear for the
   left `L`-structure. So it is an `L`-algebra homomorphism, and it
   satisfies the displayed formula by construction.
2. *It is surjective (Dedekind).* The image is an `L`-subspace. If it were
   proper, some nonzero `L`-linear functional `x ↦ ∑ σ, c σ * x σ` would
   vanish on it. Evaluating at `1 ⊗ b` gives `∑ σ, c σ * σ b = 0` for every
   `b`. By Dedekind–Artin linear independence of distinct field
   homomorphisms, every `c σ = 0`, which is a contradiction. Only finiteness of
   `L/k` is used here.
3. *The dimensions agree (Galois).* Over `L`, the source has dimension
   `[L : k]`: it is the base change of the `k`-vector space `L`. The target
   has dimension `#Gal(L/k)`. For a finite Galois extension these numbers are
   equal (`IsGalois.card_aut_eq_finrank` in Mathlib). A surjective linear map
   between `L`-vector spaces of the same finite dimension is bijective, so
   the map is an `L`-algebra equivalence.

The Galois hypothesis cannot be dropped. Any `L`-linear bijection between the
two sides forces `[L : k] = #Gal(L/k)`, and a finite extension satisfying that
equality is Galois (`IsGalois.of_card_aut_eq_finrank`). Neither step needs a
perfect base field or a characteristic restriction, which is why the scope
covers imperfect fields and positive characteristic.

## Provenance

This is an internal, derived statement; no original-source tuple is cited.
The isomorphism `L ⊗_k L ≅ ∏_{σ ∈ Gal(L/k)} L` for a finite Galois extension
is classical textbook algebra. The rationale above gives a complete,
self-contained argument for it, using only Dedekind–Artin independence of
characters and the count `#Gal(L/k) = [L : k]`. The exact Lean packaging is
the project's own choice, made for the Čech-descent consumer:

- `L`-algebra structure from the first factor;
- target `Gal(L/k) → L` with constant structure map;
- the pure-tensor formula `a * σ b`.

The statement does not claim that any source states this exact formulation.

## Scope and consumer boundary

Worker 1347 requested this statement as a prerequisite for the
simply connected central-cover existence task
`a41119fb-a633-4b81-a979-4b08e9ddbb15`. There the overlap
`Spec L ×_{Spec k} Spec L` of a finite Galois splitting cover has coordinate
algebra `L ⊗[k] L`. This proposition supplies only the algebraic
decomposition of that coordinate ring and the identification of its two
coordinate maps.

The following remain obligations of the consumers:

- transport to a coproduct of copies of `Spec L` at the scheme level;
- the group-scheme Čech cocycle;
- descent itself.

The published `Langlands.GroupScheme.SimplyConnectedCoverExistenceStatement`
pair is neither imported nor changed.

Proving the proposition is a separate exact-target proof obligation.

## Imports

`Mathlib.FieldTheory.Galois.Basic` (Galois extensions and the `Gal(L/k)`
notation) and `Mathlib.RingTheory.TensorProduct.Basic` (the algebra tensor
product and its left algebra structure). The environment is pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
