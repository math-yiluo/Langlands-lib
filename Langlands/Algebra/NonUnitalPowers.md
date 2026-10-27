# Positive products, nilpotence and actual unitization comparisons

Authors: Worker 6 (formulations, proofs and prose of the shared draft) and Worker 772 (final revision, module documentation and checks).

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, Appendix B.II and B.III, printed pages 272–273 / PDF pages 278–279. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Both proofs begin by replacing a possibly nonunital complex algebra `A` by its unitization `Ã = A ⊕ ℂ1_A`. The Schur lemma of B.II then works with a unital module. The separation lemma of B.III concerns an algebra of countable dimension and a non-nilpotent element. This module supplies elementary algebraic and dimension details of that reduction. Its definitions and comparison laws are derived implementation content, not additional numbered results attributed to the source.

The related corrections to the 2010 edition (registered as `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF pages 18–19, entries for printed pp. 314–315) concern the same two passages. One adds the hypothesis that the module is a complex vector space in Schur's lemma. The other replaces the step via right zero divisors in the separation lemma by left noninvertibility. Both corrections are already reflected in the governing 2026 text. They do not replace the 2026 statements or add hypotheses here.

## Positive products and nilpotence

For a carrier `A` with a multiplication, `Langlands.Algebra.successorPower a n` is the product of exactly `n + 1` copies of `a`, associated on the left. Index zero is `a`, and the successor is the preceding product multiplied on the right by `a`. `successorPower_zero` and `successorPower_succ` are the definitional recursion equations. No associativity is needed to define these products. For a carrier with a multiplication and a zero, `Langlands.Algebra.IsNonUnitalNilpotent a` means that some positive product `successorPower a n` is zero. These definitions do not equip the original carrier with a multiplicative identity or a natural-power instance.

In an ordinary monoid, `successorPower_eq_pow` proves by induction on `n` that the recursive product equals `a ^ (n + 1)`. The successor step unfolds one recursion step, applies the induction hypothesis and rewrites with `pow_succ`. In a monoid with zero, `isNonUnitalNilpotent_iff` proves that the new predicate agrees with Mathlib's ordinary `IsNilpotent`. A vanishing positive product `a ^ (n + 1)` is an ordinary nilpotence witness. Conversely, from `a ^ n = 0` one more multiplication by `a` gives `a ^ (n + 1) = 0`. This also covers a witness `n = 0`, which occurs only in a trivial monoid with zero. So this comparison needs no nontriviality premise.

`map_successorPower` proves by induction that an actual nonunital ring homomorphism `f : A →ₙ+* B` preserves each positive product: `f (successorPower a n) = successorPower (f a) n`. It uses only `map_mul`. It is stated for arbitrary nonunital, not necessarily associative semirings `A` and `B` in independent universes. This includes all nonunital rings.

## The actual unitization

For the unitization laws, `k` is any commutative ring and `A` any nonunital associative ring with `Module k A`, `IsScalarTower k A A` and `SMulCommClass k A A`. These express the compatible bilinear scalar multiplication under which Mathlib's actual `Unitization k A` is a ring. The scalar and algebra universes are independent.

`inr_successorPower` states that the actual embedding `Unitization.inr` sends `successorPower a n` to `(Unitization.inr a) ^ (n + 1)`. Its proof inducts on `n`. The zero case is closed by `simp`, since `successorPower a 0 = a` and a first power is the element itself. The successor case rewrites only the product side with the recursion, `Unitization.inr_mul` and the induction hypothesis, and closes with `pow_succ`.

`isNilpotent_inr_iff` states exactly that `IsNilpotent (Unitization.inr a : Unitization k A)` is equivalent to `IsNonUnitalNilpotent a`. For the forward direction, a vanishing `n`th power of the image gives a vanishing `(n + 1)`st power. By `inr_successorPower` this power is the image of `successorPower a n`, and the injectivity `Unitization.inr_injective` reflects its vanishing back to `A`. For the reverse direction, the image of a vanishing positive product is the vanishing `(n + 1)`st power of the image. Neither `k` nor `A` is assumed nontrivial. Zero algebras and zero scalar rings are allowed.

## Countable rank

For a field `k` and any `k`-vector space `A`, `unitization_countableRank_iff` states that the `k`-rank of `Unitization k A` is at most `Cardinal.aleph0` if and only if the `k`-rank of `A` is at most `Cardinal.aleph0`. No multiplication on `A` is used. Ranks are Mathlib's cardinal-valued `Module.rank`, with no finite-dimensionality premise. The scalar and carrier universes are independent.

The proof first transports the rank along the actual `k`-linear equivalence `Unitization.linearEquiv k k A : Unitization k A ≃ₗ[k] k × A`. The product formula `rank_prod` then gives `Cardinal.lift (Module.rank k k) + Cardinal.lift (Module.rank k A)`, with the cardinal lifts needed for the independent universes. Mathlib's division-ring dimension theory supplies the freeness of vector spaces that `rank_prod` uses; this is not an added premise. Finally `Module.rank_self`, `Cardinal.lift_one`, `Cardinal.add_le_aleph0`, `Cardinal.lift_le_aleph0` and `Cardinal.one_le_aleph0` reduce the bound on the sum to the bound on the rank of `A`. Thus the unitization preserves and reflects the finite-or-countable dimension condition of the source.

## Scope

The module constructs no action or invariant-subspace lattice. It proves no simplicity, finite-generation or Noetherian comparison, and no Schur, Amitsur or separation result. Those obligations belong to the compatible action and linear intertwiner tasks, the unitized Hom/lattice/endomorphism tasks and the source theorem tasks. All results here are short intrinsic laws for the positive-product construction and the same actual unitization.
