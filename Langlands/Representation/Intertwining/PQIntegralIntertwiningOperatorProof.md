# Renard VII.3.4: proof of the integral form of `J_{Q|P}`

Author: Worker 48. Module `Langlands.Representation.Intertwining.PQIntegralIntertwiningOperatorProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

This module proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.PQIntegralIntertwiningOperatorStatement`
(module `Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements`, unchanged) by
the theorem

```
theorem pqIntegralIntertwiningOperator : PQIntegralIntertwiningOperatorStatement.{u, v}
```

with no added hypothesis. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, VII.3.4, printed pp.235–236 / PDF pp.241–242. Literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard recalls that the natural isomorphism `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ≃ E` "est obtenu par
passage au quotient à partir du morphisme `F̃^{<1̄}_{PQ} → E`,
`f ↦ ∫_{U∩N\U} f(u) dν(u) = ∫_{U∩N̄} f(u) du`". He derives this from formula (VI.5.1.12), with
the equality of the two integrals coming from `U = (U ∩ N)(U ∩ N̄)`. Then the Proposition: for
`PQ`-regular `σ`, `J_{Q|P}(σ)` is the unique intertwining operator with
`J(f)(1) = ∫_{N̄∩U} f(u) du` on `F̃^{<1̄}_{PQ}(E)`.

## Structure

The published statement has two clauses. Clause (a) is the integral identification above.
Clause (b) is the uniqueness of the integral-normalized operator for `PQ`-regular `σ`. The Library
reduction `pqIntegralIntertwiningOperator_of_identification` (module
`PQIntegralIntertwiningReduction`) derives the whole statement from clause (a), stated there as
`PQIntegralIdentificationStatement`, using the proved `pqIntertwiningOperator` for clause (b).
This module proves clause (a) as `pqIntegralIdentification` and concludes:

```
theorem pqIntegralIntertwiningOperator : PQIntegralIntertwiningOperatorStatement.{u, v} :=
  pqIntegralIntertwiningOperator_of_identification pqIntegralIdentification.{u, v}
```

The proof of clause (a) does not use formula (VI.5.1.12). It defines the integral map directly,
proves it surjective, natural in `σ` and equivariant, and then uses the Library's natural
identification (`pqSupportGraded`) only through a rigidity argument.

## `exists_radical_product_homeomorph`

Renard's decomposition `U = (U ∩ N)(U ∩ N̄)` on rational points, as a homeomorphism.
Multiplication `(N ∩ U)(F) × (N̄ ∩ U)(F) → U(F)`, `(a, b) ↦ a b`, is a homeomorphism, the factors
being read as subgroups of `U(F)`. Hypotheses: `G` connected reductive over a nonarchimedean
local field, `P = M N`, `Q = M U` and `P̄ = M N̄` parabolics with `l ≫ p = lQ ≫ q`,
`lb ≫ pb = l ≫ p`, and `P(F) ∩ P̄(F) = M(F)`. Proof: as in the published
`pointImage_radical_eq_mul`, parabolic root presentations identify `N`, `U` and (by
`oppositeDynamicParabolicUniqueness`) `N̄` with dynamic unipotent subgroups. The Library
homeomorphism `MatrixRepresentation.unipotentIntersectionProduct` then applies, after rewriting
`(N̄ ⊓ U).subgroupOf U = N̄.subgroupOf U`.

## `pqIntegralIdentification : PQIntegralIdentificationStatement.{u, v}`

Fix the data of the statement and write `V = N̄(F) ∩ U(F)` with its Haar measure `haar`. The
proof first collects the geometry:

- `G(F)` is Hausdorff, second countable and σ-compact. `P(F) \ G(F)` is compact
  (`arbitraryParabolicQuotientCompact`).
- `P(F) = M(F) ⋉ N(F)`. The radicals `N(F)` and `U(F)` are closed limits of compact subgroups
  (`isLimitOfCompactSubgroups_pointImage_radical`). The Levi projection is continuous.
- `V` is closed, `V ≤ U(F)`, and `V ∩ P(F) = 1`. `M(F)` normalizes `V`, because it normalizes
  `N̄(F)` and `U(F)`.
- The product homeomorphism `(N ∩ U)(F) × V ≃ₜ U(F)` above.
- `D = P(F) Q(F)` is left `P(F)`-invariant, contains `1`, and is locally closed: it is the
  preimage of the orbit `P \ P Q`, which is locally closed by the Library's closed orbit
  ordering. Also `Q(F) ⊆ P(F) V` (from `pointImage_radical_eq_mul`), so the orbit `P \ P V`
  equals `P \ P Q` and is locally closed.

For every smooth representation `W` of `M(F)` the proof builds a linear map
`I W : F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(W) → W`:

1. `Sb W`: the space `F̃^{<1̄}_{PQ}(W)` of induced functions vanishing on `closure D \ D`. It is
   `U(F)`-stable, and its elements have compact support on `V` by the published theorem
   `pqBoundaryVanishingCompactSupport`.
2. `φ W : Sb W → F^{<1̄}_{PQ}(W)`: the class in the Jacquet module of `U(F)`. It is surjective
   by definition of `F^{<1̄}_{PQ}` as an image.
3. `J W`: the integral `f ↦ ∫_V f(v) dv` (`IntegralIdentification.integralLinear`) descended
   along `φ W` (`LinearDescent.descend`). Its kernel condition is
   `IntegralIdentification.eq_zero_of_mem_relations`, using the right invariance
   `integralOn_smoothInduced` under `U(F)`.
4. `J W` vanishes on `F^{≤1̄}_{PQ}(W) ∩ F^{<1̄}_{PQ}(W)`. A class there comes from a function
   vanishing on `closure D`, which contains `V`, so its integral is `0`. `I W` is the induced map
   on the quotient. It sends the class of `f ∈ F̃^{<1̄}_{PQ}(W)` to `∫_V f(v) dv` (`hI`).
5. `I W` is surjective (`IntegralIdentification.exists_integralOn_eq` with the set `D`), and
   natural in `W`. Naturality holds because the induced map on functions is composition, and dual
   integrals commute with linear maps.
6. Twisted equivariance: for `m ∈ M(F)` with image `m̃` in `Q(F)`, the Jacquet action is
   `m · [f] = δ_Q^{-1/2}(m̃) [f(· m̃)]` (`normalizedJacquetFunctor_obj_apply`). With the Levi
   covariance `integralOn_smoothInduced_levi` this gives `I W (m x) = χ(m) W(m)(I W x)`, where
   `χ(m) = δ_Q^{-1/2}(m̃) · leviFactor(m̃)` does not depend on `W`.

The last clause of the published `pqSupportGraded` gives a natural equivariant identification
`e W : F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(W) ≃ W`.
`SmoothRep.exists_equiv_of_natural_surjective` (module `PQIntegralIdentificationAbstract`) then
shows `χ = 1`, using the trivial representation, and that each `I W` is injective, by rigidity.
So `I σ` is an equivariant linear equivalence `E`. For `f ∈ F̃^{<1̄}_{PQ}(σ)` and `y = [f]`,
`E (proj y) = ∫_V f(v) dv`. `hasDualIntegral_integralOn` gives, for every linear form `ℓ`, the
integrability of `v ↦ ℓ(f(v))` and `ℓ(E(proj y)) = ∫_V ℓ(f(v)) dv`. This is clause (a).

## Remarks

- The proof of `pqIntegralIdentification` is checked under `set_option maxHeartbeats 6400000`.
  The final elaboration of the large term needs more than the default budget.
- Helper modules: `Langlands.Representation.Intertwining.PQIntegralIdentificationAbstract` and
  `Langlands.Representation.Intertwining.PQIntegralIdentificationGroup`.
- Published results used: `pqIntegralIntertwiningOperator_of_identification`, `pqSupportGraded`,
  `pqBoundaryVanishingCompactSupport`, `pointImage_radical_eq_mul`,
  `arbitraryParabolicQuotientCompact`, `representedGeometricLemma` (finiteness of
  `P \ G / Q`), `Geometric.closedSubgroupOrbitOrdering`, and
  `MatrixRepresentation.unipotentIntersectionProduct`.
