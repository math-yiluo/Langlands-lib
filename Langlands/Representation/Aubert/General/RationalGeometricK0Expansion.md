# Proof of the rational geometric-lemma K0 expansion

Module: `Langlands.Representation.Aubert.General.RationalGeometricK0Expansion`,
namespace `Langlands.Aubert.General.RationalPointFamily`. Author: Worker 4021.

`rationalGeometricK0Expansion : RationalGeometricK0ExpansionStatement.{u, v}`
proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalGeometricK0ExpansionStatement`
of `Langlands.Representation.Aubert.General.RationalGeometricK0Target`. It proves
the whole unapplied proposition, with independent universe parameters `u` and `v`
and no theorem parameters of its own. The statement's Lean/Markdown pair and the
pairs it imports are unchanged.

Its content is the geometric lemma on exact K0. Take every nonarchimedean local
field and every connected reductive group over it, with its actual maximal split
torus, generic cocharacter and literal simple-root labels. Then, for all standard
subsets `I`, `J` and every section of the actual normalizer quotient, the
composite `r_I ∘ i_J` of normalized induction and normalized Jacquet restriction
on exact K0 is the sum, over the minimal representatives `minimalReps cs I J`, of
the actual normalized intersection terms `geometricTermK0 I J (lift w)`. All
premises of the target are kept at their displayed scopes.

## Proof as implemented

The proof is a single application:

```
rationalGeometricK0Expansion_of_standardParabolicPoints.{u, v}
  GroupScheme.standardParabolicPointsStatement_proof.{u}
```

- `rationalGeometricK0Expansion_of_standardParabolicPoints` (module
  `RationalGeometricK0Assembly`) proves
  `StandardParabolicPointsStatement.{u} → RationalGeometricK0ExpansionStatement.{u, v}`.
  It introduces the target's binders. It then applies
  `geometricK0Expansion_of_points_of_balance` (module
  `RationalGeometricK0Reduction`) to them, to its points premise, and to the
  epsilon cancellation `geometricEpsilon_mul_eq_one` (module
  `RationalGeometricEpsilonBalance`) for every `I`, `J` and normalizer point
  `n`.
- `GroupScheme.standardParabolicPointsStatement_proof` (module
  `Langlands.GroupScheme.Rational.StandardParabolicPointsProof`) is the published
  premise-free proof of `StandardParabolicPointsStatement.{u}`. That statement
  covers the Borel–Tits structure of the standard parabolic rational points,
  including the indexing `W_J \ W / W_K ≃ P_J(k) \ G(k) / P_K(k)` of parabolic
  double cosets by normalizer points.

The two module pairs `RationalGeometricEpsilonBalance` and
`RationalGeometricK0Assembly` were accepted in candidate
`e2fd2fa3-87f4-473e-9cb2-68e1dea097b2`. This module only composes them with the
published points theorem.

## The argument behind the composed declarations

1. **Support filtration** (`ParabolicSupportFiltration`). The Jacquet module of
   an induced representation has a filtration by the support on the
   `P_J`-orbits in `G/P_I`. It is built from the closed-subgroup Mackey filtration
   and exactness of character localization. Its graded pieces are the localized
   orbit pieces (`jacquetSupportOrbitIso`).
2. **Orbit ordering** (`RationalGeometricOrbitOrdering`). The points theorem
   identifies `P_J \ G / P_I` with the Weyl double cosets. The orbits are then
   ordered by lifts of the minimal representatives (`minimalOrbitOrdering`). This
   handles the inversion between the orbit convention `P_J w⁻¹` and the target's
   `W_I \ W / W_J`.
3. **Graded pieces** (`RationalGeometricOrbitSource`, `RationalGeometricOrbitTerm`).
   Each orbit piece is naturally isomorphic to the actual normalized geometric
   term, twisted by the two Haar correction characters `ε₁ ε₂`. This uses the
   normalized compact comparison, the compact/smooth induction comparison and
   compactness of the parabolic quotient of the common Levi.
4. **Epsilon cancellation** (`RationalGeometricEpsilonBalance`).
   `ε₁ ε₂ = 1` holds on the literal common Levi
   `(M_I ∩ n M_J n⁻¹).subgroupOf M_I`. This is proved by realizing that Levi as a
   dynamic centralizer and applying the five-factor Haar balance through the
   common centralizer. Character-restriction injectivity comes from the published
   split-component results, so the corrections are cancelled rather than
   discarded.
5. **K0** (`RationalGeometricK0Reduction`).
   `SmoothRep.filtrationGrothendieckStatement` turns the finite filtration and the
   graded comparisons into the class sum. `FiniteLengthGrothendieckGroup.hom_ext_object`
   then identifies the two integer-linear maps.

## Dependencies

Proof-body dependencies of this theorem:

- `rationalGeometricK0Expansion_of_standardParabolicPoints`, whose body uses
  `geometricK0Expansion_of_points_of_balance` and `geometricEpsilon_mul_eq_one`;
- `GroupScheme.standardParabolicPointsStatement_proof`, whose body uses
  `rationalBruhat` and `rootRankOneFactorization`.

Transitive uses of the listed representation theorems, by scope:

- **Geometric lemma.** This theorem is the general rational-point geometric
  lemma on exact K0 (BZ77 2.12/5.2, Renard VI.5.1). Its proof assembles the
  geometric filtration from the published closed-subgroup Mackey filtration and
  support filtration in the chain above. No geometric-lemma expansion and no
  orbit-functor comparison is assumed as a premise.
- **Adjointness, cuspidal support, character independence, Langlands
  classification.** The proof bodies of this theorem, of the two assembly
  declarations, of the modules in steps 1–5, and of
  `standardParabolicPointsStatement_proof` invoke none of these. The cancellation
  in step 4 detects rational characters of tori algebraically. It does not use
  linear independence of representation characters.

The imported module closure is larger than these proof-body dependencies. The
theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

The scope is the target's: every connected reductive group scheme over every
nonarchimedean local field, including positive characteristic and nonsplit or
non-quasisplit groups. The topology is `pointTopology`, the labels are the literal
`SimpleRoot i ν`, and empty or full `I` and `J` are allowed. No premise is added
beyond the target's own, and `RootLengthComparison` and
`PositiveSimpleReflectionComparison` stay among its premises. Aubert
Proposition 3.2 and the application to Theorem 3.6 are not used as evidence.
