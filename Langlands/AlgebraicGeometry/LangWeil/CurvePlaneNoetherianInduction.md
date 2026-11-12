# Noetherian induction for uniform bounds over fields

Lean module: `Langlands.AlgebraicGeometry.LangWeil.CurvePlaneNoetherianInduction`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

Author: Worker 189. This module is a helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581).
Provenance: internal. It is the standard Noetherian induction on the spectrum of a Noetherian
ring, in the algebraic form needed by `FamilyCurvePlaneReduction`. It is not a cited theorem.

## Statement `exists_uniform_of_forall_prime`

Let `A` be a Noetherian ring. Let `Φ B κ` be a proposition depending on a natural number `B`
and a field `κ` (in a fixed universe) with an `A`-algebra structure. Assume:

- `Φ` is monotone in `B`: `B ≤ B'` and `Φ B κ` imply `Φ B' κ`;
- (local bounds) for every prime ideal `p` of `A` there are `a ∉ p` and `B` such that `Φ B κ`
  holds for every field `κ` in which all elements of `p` map to `0` and `a` maps to a nonzero
  element.

Then there is one `B` with `Φ B κ` for every field `κ` with an `A`-algebra structure.

Geometrically: the bound holds on a nonempty open `D(a)` of each irreducible closed subset
`V(p)` of `Spec A`, and so on all of `Spec A`.

## Proof

It suffices to prove, for every ideal `I`, that some `B` works for all fields killing `I`;
the case `I = ⊥` is the claim. This is proved by well-founded induction on `I` for the reverse
inclusion order (`WellFoundedGT.induction`; ideals of a Noetherian ring satisfy the ascending
chain condition).

- If `I = ⊤` no field kills `I` (it would kill `1`), so `B = 0` works.
- Otherwise, for each minimal prime `q` over `I`, take the local data `a ∉ q`, `B₁` at `q`.
  The ideal `q ⊔ (a)` strictly contains `I` (it contains `a ∉ q ⊇ I`), so the induction
  hypothesis gives `B₂` for fields killing `q ⊔ (a)`. For a field killing `q`, either `a`
  maps to `0`, so the field kills `q ⊔ (a)` and `B₂` works, or `a` maps to a nonzero element
  and `B₁` works. By monotonicity `max B₁ B₂` works for every field killing `q`.
- `I` has finitely many minimal primes (`Ideal.finite_minimalPrimes_of_isNoetherianRing`).
  Take `B` the supremum of the bounds for them. The kernel of `A → κ` is a prime containing
  `I`, so it contains some minimal prime `q` over `I` (`Ideal.exists_minimalPrimes_le`), and
  the bound for `q` applies; monotonicity gives `B`.
