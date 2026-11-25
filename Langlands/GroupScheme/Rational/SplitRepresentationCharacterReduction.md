# The character theorem from the highest-weight classification

This module proves

```text
splitRepresentationCharacterStatement_of_classification :
  SplitHighestWeightClassificationStatement.{u} → SplitRepresentationCharacterStatement.{u}
```

So Milne's character theorem (Theorem 22.38, the statement
[`Rational.SplitRepresentationCharacterStatement`](SplitRepresentationCharacterStatement.md))
follows from the fundamental theorem of highest weight over the same field (the statement
[`Rational.SplitHighestWeightClassificationStatement`](SplitHighestWeightClassificationStatement.md)).
The hypothesis is applied to the same `k`, `G` and `p`. Conjunct 1 of the conclusion does
not use it. Conjunct 2 uses conjuncts 2 and 3 of the classification, and conjunct 3 uses
conjunct 1 of the classification. The theorem itself proves neither statement outright.

Throughout, `k` is a field, `G` an affine group scheme over `Spec k`, `p : SplitPinning G`,
and `ch ρ lam` stands for `Module.finrank k (p.representationWeightSpace ρ lam)`. The
proof works with the modules over the operator algebra of
[`MatrixRepresentation.OperatorModule`](../MatrixRepresentation/OperatorModule.md) and
their weight spaces from [`Rational.SplitWeightModule`](SplitWeightModule.md).

## Nonzero weight spaces

`representationWeightSpace_ne_bot_iff_weightSubmodule`: the weight space of `ρ` is nonzero
exactly when the weight space of `OperatorModule ρ` is. `representationWeightSpace_ne_bot_of_finrank_ne_zero`
is immediate.

## Conjunct 1: finite support and reflection invariance

- `finite_support_nat_finrank_representationWeightSpace`: the support of `lam ↦ ch ρ lam` is
  contained in the finite set of `lam` with nonzero weight space
  (`finite_weightSubmodule_ne_bot_operatorModule`).
- Reflection invariance is the Library theorem
  `SplitPinning.finrank_representationWeightSpace_root_reflection` (module
  [`Rational.HighestWeightRootEndpoint`](HighestWeightRootEndpoint.md)).

## Conjunct 2: semisimple representations are determined by their characters

`exists_isHighestWeight_of_isSimpleModule` (uses classification conjunct 3). Let `M` be a
realized module, `S` a simple submodule of `M` with a nonzero weight space for `lam`, and
suppose `lam` is maximal among the weights of `M`: every weight `mu` of `M` with
`mu - lam ∈ p.positiveRootMonoid` equals `lam`. Then `S` is isomorphic to
`OperatorModule τ` for some `τ : MatrixRepresentation G (Fin r)` with
`p.IsHighestWeight τ lam`.

Proof: `IsRealized.exists_linearEquiv` gives `τ` with `OperatorModule τ ≅ S`. `τ` is
irreducible (`isIrreducible_of_isSimpleModule`), so classification conjunct 3 gives a
weight `lam'` with `p.IsHighestWeight τ lam'`. Since `lam` is a weight of `τ`, the last
component of `IsHighestWeight` gives `lam' - lam ∈ p.positiveRootMonoid`. Since
`ch τ lam' = 1`, `lam'` is a weight of `M`. Maximality gives `lam' = lam`.

`nonempty_linearEquiv_of_finrank_weightSubmodule_eq` (uses classification conjuncts 2
and 3). Two realized semisimple modules `M`, `N` whose weight spaces have the same
dimensions for every `lam` are isomorphic. The proof is by strong induction on
`finrank k M`:

- If every weight space of `M` is zero, then `M = 0`
  (`eq_zero_of_isRealized_of_weightSubmodule_eq_bot`). The weight spaces of `N` are then
  zero too, so `N = 0` and `M ≅ N`.
- Otherwise the finitely many weights of `M` have a maximal element `lam` for the order of
  `p.positiveRootMonoid` (Library `Langlands.RootDatum.Triangular.exists_maximal_of_finset`).
  `M` and `N` have the same weights, so `lam` is also maximal for `N`. By
  `exists_isSimpleModule_weightSubmodule_ne_bot_of_isRealized`, `M` and `N` have simple
  submodules `S` and `S'` with nonzero weight spaces for `lam`. By the previous lemma, both
  are modules of representations with highest weight `lam`. Classification conjunct 2
  (from right to left, with `lam = lam`) gives a bijective intertwining matrix between
  them, hence `S ≅ S'` (`Intertwines.toLinearEquiv`). Choose complements `T` of `S` and
  `T'` of `S'` (Mathlib's `exists_isCompl` in a semisimple module). By additivity
  (`finrank_weightSubmodule_eq_add_of_isCompl`) and `S ≅ S'`, `T` and `T'` have the same
  weight dimensions. They are realized and semisimple, and `finrank k T < finrank k M`
  because `S ≠ 0`. By induction `T ≅ T'`, and `M ≅ S × T ≅ S' × T' ≅ N`
  (`Submodule.prodEquivOfIsCompl`).

`exists_intertwines_bijective_of_finrank_eq` is conjunct 2 itself. For representations
`ρ`, `σ` in coordinates `Fin n`, `Fin m` satisfying the statement's `IsSemisimpleRep`,
the modules `OperatorModule ρ`, `OperatorModule σ` are semisimple
(`isSemisimpleModule_of_sSup_eq_top`) and realized. Their weight dimensions are `ch ρ`
and `ch σ` (`finrank_weightSubmodule_operatorModule`). The previous lemma gives a module
isomorphism, and `exists_intertwines_bijective_of_linearEquiv` turns it into a matrix `C`
with `ρ.Intertwines σ C` and `Function.Bijective C.mulVecLin`.

## Conjunct 3: characters span the invariants

`exists_sub_of_reflection_invariant` (uses classification conjunct 1). Let `S` be the set
of functions `characterLattice p.torus →₀ ℤ` of the form `ch ρ - ch σ` for representations
`ρ`, `σ` in coordinates `Fin n`, `Fin m`. It is an additive subgroup:

- `0 = ch ζ - ch ζ`, for the representation `ζ` of
  `exists_finrank_representationWeightSpace_eq_zero`;
- sums are handled by direct sums (`exists_finrank_representationWeightSpace_eq_add`
  applied to the positive parts and to the negative parts);
- negation swaps `ρ` and `σ`.

For each dominant `lam`, classification conjunct 1 gives `ρ` with
`p.IsHighestWeight ρ lam`. The function `c = ch ρ` (finitely supported by conjunct 1) lies
in `S` (subtract the zero character). It is invariant under the reflection group (Library
`Langlands.LinearAlgebra.DominantTriangular.isInvariant_reflectionGroup_of_reflection`
together with `finrank_representationWeightSpace_root_reflection`). It satisfies `c lam = 1`,
and every `mu` with `c mu ≠ 0` satisfies `lam - mu ∈ p.positiveRootMonoid` (components
three and four of `IsHighestWeight`). The Library's triangular spanning theorem
`Langlands.LinearAlgebra.DominantTriangular.isInvariant_mem_of_triangular` (module
`LinearAlgebra.DominantTriangularInvariants`), applied to `S` as a `ℤ`-submodule, then shows
that every reflection-group-invariant function lies in `S`. Invariance of the given `f`
under the reflection group follows from its invariance under each `s_i` by the same
Library lemma.

## Assembly

`splitRepresentationCharacterStatement_of_classification` introduces `k`, `G`, `p`, splits
the classification hypothesis at `k`, `G`, `p` into its three conjuncts, and returns the
three conjuncts above.

## Provenance

The route follows Milne, *Algebraic Groups* (2017), Theorem 22.38 and its proof (printed
pp. 474–475), registered as `milne-2017-algebraic-groups`, as outlined in the section "For
the later proof" of the statement's Markdown. Two points differ in form. Injectivity is
proved directly for semisimple representations by peeling off a simple summand of maximal
weight, instead of comparing multiplicities of the `V(λ)` in the Grothendieck group.
Surjectivity uses the Library's triangular spanning theorem, which inducts on the
`W`-invariant form instead of Milne's Zorn argument.
