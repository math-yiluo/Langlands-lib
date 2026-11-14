# Geometric regularity and differentials over the prime field

`Langlands.CommutativeAlgebra.Popescu.GeometricRegularityKaehlerInjectiveStatement` (universe `u`).

## Hypotheses

- `k` is a field of characteristic `p > 0` (`[Fact p.Prime] [CharP k p]`).
- `Λ` is a `k`-algebra that is geometrically regular over `k`. This is the Library predicate
  `GeometricallyRegular k Λ` from `Langlands.CommutativeAlgebra.RegularRingMaps`, which includes that
  `Λ` is Noetherian.
- `q` is a prime of `Λ`, with `A = Λ_q` (`Localization.AtPrime q`) and `K = κ(q)`
  (`q.ResidueField`).

## Conclusion

The canonical `K`-linear map

`K ⊗_k Ω_{k/ℤ} → K ⊗_A Ω_{A/ℤ}`,  `c ⊗ ω ↦ c · (1 ⊗ ω|_A)`

is injective. Here `ω|_A` is the image of `ω` under `KaehlerDifferential.map ℤ ℤ k A`, the map
`Ω_{k/ℤ} → Ω_{A/ℤ}` induced by `k → A`.

In Lean the map is `LinearMap.liftBaseChange K f`, where
`f = (TensorProduct.mk A K Ω[A⁄ℤ] 1).restrictScalars k ∘ₗ (KaehlerDifferential.map ℤ ℤ k A).restrictScalars k`.

## Source

Stacks Project, More on Algebra, Proposition 15.36.1 (Tag 07E5). The registered snapshot is in
`stacks-geometric-regularity-07E5-07E6-2026-11-14`.

The proposition concerns a field `k` of characteristic `p > 0` and a Noetherian local `k`-algebra
`(A, 𝔪, K)`. It states that condition (1), "`A` is geometrically regular over `k`", is equivalent to
condition (4), "`A` is regular and the map `Ω_{k/𝔽_p} ⊗_k K → Ω_{A/𝔽_p} ⊗_A K` is injective".

This statement records the injectivity part of (1) ⇒ (4), applied to `A = Λ_q`. The Stacks proof
goes through (2) and is due to Faltings.

## Encoding

- **Base ring.** The base is `ℤ` instead of `𝔽_p`. For a ring `B` of characteristic `p`, the
  canonical map `Ω_{B/ℤ} → Ω_{B/𝔽_p}` is an isomorphism, because `ℤ → 𝔽_p` is surjective. Using `ℤ`
  avoids choosing a `ZMod p`-algebra structure. Its algebra structures are the canonical ones.
- **Localization.** The statement is phrased at a prime `q` of a geometrically regular `Λ`. `Λ_q` is
  geometrically regular over `k` as a localization of `Λ`.
- **Regularity.** The regularity of `A`, the other half of (4), is not part of the statement.
- **Universes.** All types are in one universe `u`.

## Use

Together with the Jacobi–Zariski sequences for `ℤ → k → K` and `ℤ → A → K`, this statement implies
`GeometricRegularityH1InjectiveStatement` (07E5 (1) ⇒ (3)). That step is the equivalence (3) ⇔ (4)
in the Stacks proof.
