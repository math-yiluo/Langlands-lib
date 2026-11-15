# Lifting field maps in characteristic `p` along square-zero extensions

This module supports the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.1
(Tag 07FG), in `ArtinianFlatSubalgebra`. All declarations are in the namespace
`Langlands.CommutativeAlgebra.Popescu.ArtinianFlat`.

The source uses that a field of characteristic `p` is formally smooth over `𝔽_p`
(Algebra, Lemma 158.7, Tag 0320; `𝔽_p` is perfect, so every extension of it is separable)
to choose the section `σ : K → Λ`, to lift `σ'` to `σ`, and to lift `τ' : k → A'` to `τ`.
In this formalization it is used twice, both times in the inductive step of the claim
(`coeffClaim_of_surjective` in `ArtinianFlatClaim`): to lift `σ'` and to lift `τ'`. Only
one consequence is needed: a ring map from a field `K` of characteristic `p` into `B ⧸ J`
lifts to `B` if `J² = 0` and `p = 0` in `B`. The module proves this directly, without
`p`-bases or the cotangent complex.

## Declarations

- `SqLift J g` (structure): for an `E`-algebra map `g : K → B ⧸ J`, a partial lift of `g`. It
  consists of an intermediate field `carrier` of `K / E` and an `E`-algebra map
  `emb : carrier → B` with `mk ∘ emb = g` on `carrier`. Its partial order is "extends"
  (inclusion of carriers, compatible maps). `⊥` is the lift on `E` given by the structure map
  of `B`.
- `directed_carrier`, `union c hc`, `le_union`: a nonempty chain of partial lifts has an upper
  bound. Its carrier is the supremum of the carriers and its map is `Subalgebra.iSupLift`. This
  follows the union construction for `IntermediateField.Lifts` in Mathlib's
  `FieldTheory/Extension.lean`.
- `exists_ge_of_adjoin x h1 y hy hyg`: let `s` be integral over `x.carrier` and `y ∈ B` a root
  of the minimal polynomial of `s` (mapped by `x.emb`) with `mk y = g s`. Then `x` extends to a
  partial lift whose carrier contains `s` (`PowerBasis.lift` on `carrier⟮s⟯`).
- `pow_eq_pow_of_sub_mem`: if `J² = 0` and `a − b ∈ J`, then `aᵖ = bᵖ`. Indeed
  `(a − b)ᵖ = 0` and `(x + y)ᵖ = xᵖ + yᵖ` in characteristic `p`.
- `frobLift p hJ g : K →+* B`: the map `x ↦ s(g x)ᵖ`, where `s` is any set-theoretic section of
  `B → B ⧸ J`. By `pow_eq_pow_of_sub_mem` the value does not depend on the choice of lift, and
  the map is additive and multiplicative. `frobLift_apply` and `mk_frobLift` record
  `frobLift x = aᵖ` for every lift `a` of `g x`, and `mk (frobLift x) = g (xᵖ)`.
- `frobEquiv p : K ≃+* K^p` (Frobenius onto its image) and `coe_frobEquiv`.
- `exists_lift_of_sq_zero_aux p hJ g`: every ring map `g : K → B ⧸ J` lifts to `K → B`.
  **Proof.**
  1. Let `E = K^p`. Then `B` is an `E`-algebra via `ρ = frobLift ∘ frobEquiv⁻¹`, and `g` is
     `E`-linear (`mk_frobLift`).
  2. By Zorn's lemma there is a maximal partial lift `φ` (chains are bounded by `union`).
  3. Suppose `φ.carrier ≠ K` and pick `α ∉ φ.carrier`. Then `c = αᵖ ∈ E ⊆ φ.carrier`, and
     `Xᵖ − c` is irreducible over `φ.carrier` (`X_pow_sub_C_irreducible_of_prime`; a root `b`
     in the carrier would give `bᵖ = αᵖ`, so `b = α`). Hence it is the minimal polynomial of
     `α`.
  4. Pick any lift `y` of `g α`. Then `yᵖ = frobLift α = ρ(c) = φ.emb(c)`, so `y` is a root of
     the minimal polynomial. `exists_ge_of_adjoin` extends `φ`, contradicting maximality.
  5. So `φ.carrier = K`, and `φ.emb` composed with `K ≅ ⊤` is the lift.
- `exists_lift_of_sq_zero p f hf hsq g`: the same for a surjection `f : B → B'` whose kernel
  has square zero. It applies the quotient form to `B ⧸ ker f ≅ B'`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), proof of Lemma 11.1 (Tag 07FG, printed
pp. 25-26): "As `K` is formally smooth over `𝔽_p` (see Algebra, Lemma 158.7) we can find a
ring map `σ : K → Λ` which is a section", "Choose a lift `σ : K → Λ` of `σ'`", and
"Choose a lift `τ : k → A` of `τ'` (possible as `k/𝔽_p` is formally smooth)".
