# Equal actual Jacquet totals for generic fine cuspidal induction

Author: Worker 166.

`Langlands.GLRelativeGenericJacquetTotalsStatement.{uF, uV}` is a derived
proposition definition for the two total counts used in the generic relative
constituent comparison. It supplies a statement; a separate proof must establish
it.

For every prime `p`, compatible local field `F : PadicField.{uF} p` and
`TopologicalData T`, positive rank `n`, block shape `B` and actual refinement
`S`, set `C = B.flatten S`. Let `omega : Rep.{uV} ℂ (C.Levi F.Carrier)` be
irreducible, cuspidal and unitarizable, using exactly the predicates in
[RelativeJacquetMultiplicityStatement](RelativeJacquetMultiplicityStatement.md).
Cuspidality includes admissibility. The field and inducing-carrier universes
are independent.

For arbitrary fine real vector `v0` and coarse real vector `t`, assume
`IsRelativeGenericParameter C B v0 t`. Define

```text
parent(k) = ((B.flattenBlockEquiv S).symm k).1
sigma = T.leviRealPowerTwist C (fun k => -v0(k) + t(parent(k))) omega.rho
tau = RelativeJacquetMultiplicity.fineTwist T B S omega v0 t
I = RelativeJacquetMultiplicity.innerInduced T B S tau
N = Nat.card (CuspidalSupport.AssociatingPermutations C C sigma sigma).
```

Thus `tau` is the actual pullback of `sigma` along the inverse of the constructed
flattened-Levi equivalence. The count uses the existing actual minimal
self-associating permutations, including their full-Levi conjugation and
transported representation-equivalence witnesses. It introduces no new Weyl
representatives or counting convention.

The proposition asserts both

* `HasJordanHolderMultiplicity (innerJacquet T B S I) tau N`;
* `HasJordanHolderMultiplicity (ambientJacquet T B S I) tau N`.

The first module is the normalized opposite Jacquet module inside the coarse
Levi of the full inner induction `I`. The second is the normalized composed
opposite Jacquet module of the outer induction of that same `I`. Both act on
the existing actual refined subgroup and have carrier universe `max uF uV`.
Each conjunct asserts existence of an actual finite composition series with
exactly `N` factors equivalent to `tau`. This is stronger than an equivalence
between two multiplicity predicates that might both fail.

The normalization is inherited without change: upper induction has right
translation and positive half-modulus covariance; opposite Jacquet has the
positive upper half-modulus action. The absolute value is `q^(-valuation)`.
There is no chamber inequality, intermediate discrete-series support, chosen
finite series, geometric-filtration certificate or tensor-factorization premise.

## Derived provenance and proof route

This is an internal bridge between existing Library interfaces, rather than a
literal transcription of an external source. Its intended derivation is:

1. [FineTwistRegularityStatement](FineTwistRegularityStatement.md), proved in
   [FineTwistRegularityProof](FineTwistRegularityProof.md), supplies irreducibility
   of the real twist and `tau`, admissibility, and cuspidality of `sigma`.
2. Apply
   [ProductLeviCuspidalJacquetMultiplicityStatement](ProductLeviCuspidalJacquetMultiplicityStatement.md)
   to `sigma`, using it as both inducing and test representation. Its exact
   multiplicity clause, at the cardinality it specifies, supplies an actual
   series for the first module. The initial count is the self-association subtype
   restricted to `Geometric.blockWeyl B`.
3. [RelativeGenericWeylCountStatement](RelativeGenericWeylCountStatement.md),
   proved in [RelativeGenericWeylCountProof](RelativeGenericWeylCountProof.md),
   identifies that restricted cardinality with `N`. This uses unitarity and
   relative genericity, with arbitrary `v0` and no chamber restriction.
4. For the ambient module, normalized refinement induction transitivity and
   [ComposedFlattenedInductionStatement](../Parabolic/ComposedFlattenedInductionStatement.md)
   identify the actual outer induction of `I` with standard induction from
   `C` of `sigma`. The pullback and its inverse cancel through actual
   representation equivalences.
5. The normalized clause of
   [FlattenedOppositeJacquetComparisonStatement](../Parabolic/FlattenedOppositeJacquetComparisonStatement.md)
   identifies the composed opposite quotient, after pullback to `C.Levi`,
   with the standard opposite quotient.
   [CuspidalJacquetMultiplicityStatement](CuspidalJacquetMultiplicityStatement.md)
   then supplies the count `N` for that full quotient, using the self-associated
   pair `C, C`. Actual equivariance of the opposite Jacquet functor and
   [MultiplicityTransportStatement](../Filtration/MultiplicityTransportStatement.md)
   transport its finite-series witness back to the second module above.

The two cuspidal multiplicity interfaces in steps 2 and 5 are proof dependencies.
Defining this proposition does not prove them. In particular, the conditional
[ProductLeviCuspidalJacquetAssembly](ProductLeviCuspidalJacquetAssembly.md)
alone cannot be used as an unconditional count theorem.

This statement isolates the full-induction totals. It contains no selected
constituent, positivity criterion, quotient-detection assertion or head theorem.
Further finite-series and constituent-summation arguments are required for the
host comparison. Composition-factor counts alone do not identify Hom ranks in
a potentially nonsemisimple cuspidal block or compare the opposite Jacquet module
of an actual quotient.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Compilation and Prop
inspection are development checks; independent semantic review and Library
publication remain required.
