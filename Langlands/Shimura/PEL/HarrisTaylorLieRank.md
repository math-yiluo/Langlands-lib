# Integer Lie rank forced by the Harris–Taylor central trace test

This module constructs a point-indexed finite basis cover of the actual
relative Lie sheaf and proves that the Harris–Taylor central trace test
forces its integer rank. It also identifies any separately specified
geometric relative dimension on a nonempty base.

The original source is Harris–Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed pp.89–91 / PDF pp.97–99,
especially Lemma III.1.2(3). The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The field-name convention is inherited from `HarrisTaylorLieCondition`:
the source's imaginary quadratic field `E` is `L`, its totally real field
`F⁺` is `E`, and its CM field `F` is `K`.

All declarations are in `Langlands.Shimura.HarrisTaylor`. Schemes and
coefficient algebras here have universe zero.

## From the identity trace to integer chart sizes

Let `s : S ⟶ Spec K` be the actual structure morphism, `B/S` an actual
abelian scheme, and `i : A →ₐ[ℚ] End0 B` a rational algebra action,
where `A` is also a `K`-algebra. The trace condition restricts this action
along the actual central scalar map `K → A`.

For a finite chart `e : free J ≅ B.Lie.over U` and a smaller open
`V : Over U` with nonempty underlying space,
`centralLieTraceConditionAt_card` assumes the central trace identity
at `1`. The already proved `centralLieTraceConditionAt_one` gives

```text
(card J : Γ(S, V.left)) = ([K:L] * n² : Γ(S, V.left)).
```

The actual structure map `secHom s V.left` is an injective ring map
from the number field `K` on a nonempty open. It therefore gives
characteristic zero to this section ring. Injectivity of natural-number
casts proves the natural-number equality
`Fintype.card J = Module.finrank L K * n ^ 2`.
Nilpotents in the section ring are permitted.

`centralLieTraceCondition_card` applies this result to the identity
smaller open and the all-chart trace condition. The chart open itself
must be nonempty. No integer-rank conclusion is claimed for an isolated
empty open, whose section ring does not distinguish natural numbers.

## An actual point-indexed finite Lie cover

`liePointedFiniteLocalBasisData B` reindexes the existing
`lieFiniteLocalBasisData B` by the points of `S`. For each `x : S`,
the covering property proves that some member of the existing cover
contains `x`; classical choice selects such a member and retains its
actual local generators. The new family covers `S` because its member
indexed by `x` contains `x`.

The module proves that this data is locally free and that each local
index type has a `Fintype` instance, using the original finite basis
cover. `liePointedFiniteLocalBasisData_mem` proves that each member
contains its indexing point. Thus every member used for the trace
comparison is nonempty.

`centralLieTraceCondition_lieRank` uses this cover as the witness of
`IsLocallyFreeOfRank B.Lie ([K:L] * n²)`. On each member it applies
the integer chart-size theorem and constructs an equivalence of its
basis index type with `Fin ([K:L] * n²)`. This is the actual covering
basis definition of fixed local rank. When `S` is empty, the
point-indexed family has no members, covers the empty space, and
satisfies the rank condition vacuously.

## Comparison with a specified geometric dimension

On a nonempty base, `centralLieTraceCondition_relativeDimension_eq`
takes an actual proof of `B.HasRelativeDimension g` and proves
`g = [K:L] * n²`. It uses `lieLocalFreenessRank` to obtain an actual
Lie basis cover whose index types are equivalent to `Fin g`. A base
point selects a nonempty member; the trace test determines the
cardinality of its basis. Comparing the two finite cardinalities gives
the equality. The proof does not assume a separate rank equality.

Under the explicit quadratic-extension hypotheses for `L/ℚ` and
`K/E` and the commuting rational algebra towers,
`centralLieTraceCondition_lieRank_totallyReal` and
`centralLieTraceCondition_relativeDimension_eq_totallyReal`
rewrite these conclusions using the existing
`finrank_imaginary_eq_totallyReal L K E`, namely `[K:L] = [E:ℚ]`.
Here `E` is a totally real number field.

## Provenance and scope

These are derived consequences of the implemented central trace formula,
not additional equivalences asserted from the literature. The source
assumes geometric dimension `d n²` in its running setup on printed
p.89 and in the moduli problem on p.91. Specializing its condition (3)
to `1` explains the integer-rank comparison. The implemented cover
construction and the geometric-dimension uniqueness proof use the
existing actual Lie basis and geometric-dimension-to-Lie-rank results.

The elementary rank results retain the general CM fields and rational
algebra action of the earlier trace construction, including `n = 0`.
They do not supply the source's further division-algebra, compositum,
faithfulness or signature hypotheses. They do not prove existence of
geometric relative dimension from Lie rank, its invariance under rational
isomorphism, the construction of `Lie⁺`, the compatibility equivalence
of Lemma III.1.2, or scheme-level representability.
