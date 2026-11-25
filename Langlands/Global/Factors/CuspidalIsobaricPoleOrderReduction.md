# Reduction of the cuspidal-isobaric pole order to the pair theorems

`Langlands.Global.CuspidalIsobaricPoleOrderReductionStatement` is the
implication from `CuspidalPairPoleStatement` and
`CuspidalPairBoundaryNonvanishingStatement` to
`CuspidalIsobaricPoleOrderStatement`. The theorem
`Langlands.Global.cuspidalIsobaricPoleOrderReduction` proves this implication
in both universes of the target, `u` for the number field and `uQ` for the
factor universe of the spectral presentations. The two analytic propositions
are explicit premises.

The shared assembly theorem
`Langlands.Global.cuspidalIsobaricPoleOrder_of_partialPairNonvanishingAtOne`
takes the same completed pair-pole premise and a fieldwise witness
condition `Langlands.Global.CuspidalIsobaricPoles.PartialPairNonvanishingAtOne F`.
For two split-centre-trivial cuspidal realizations with irreducible admissible
finite components and any finite set `S` containing both exceptional sets,
the condition supplies a meromorphic representative of the partial Euler
product outside `S` with order at most `0` at `1`.

## Proof

The following steps prove the shared assembly theorem.

1. Apply the pair-pole premise to each pair `(T₀, T i)` to obtain the finite
   pair choices and the archimedean parameters of the constituents. Take the
   archimedean parameters of `T₀` from `(T₀, T₀)`, which also works when the
   family is empty. For any supplied finite choices and archimedean
   parameters, the pair-pole premise supplies completed functions `Λ₀ i`.
   They are analytic off `{0, 1}` and meromorphic at both exceptional
   points, hence meromorphic on `ℂ`.
2. For any family `Λ i` of completed representatives with the same data,
   compare `Λ i` and `Λ₀ i` on a right half-plane common to both
   convergence regions. Their Euler products have the same value by
   uniqueness of `HasProd`. The meromorphic identity theorem
   `FunctionalEquationComparison.eq_on_halfplane_meromorphicEq` gives
   equality on each punctured germ. The lower bound `-1` on the order
   and the criterion for negative order therefore hold for `Λ i`.
   After substituting the rank equality, apply
   `CuspidalOperatorRealization.isContragredientOf_symm` in both directions
   to identify that criterion with the predicate counted by
   `contragredientMultiplicity`.
3. Bound the order of `Λ i` above by `0`. For this pair, let `S` be the
   union of the two exceptional sets of finite places. The fieldwise
   condition supplies the partial function over places outside `S` and
   its upper order bound at `1`. At each such place the
   spherical polynomial comparison identifies the supplied finite local
   factor with `partialEulerFactor`. On a common right half-plane,
   `Finset.hasProd` and `HasProd.mul_compl` then identify `Λ i` with the
   partial function multiplied by the factors at `S` and by the
   archimedean product. The identity theorem compares their orders at
   `1`. Each reinstated factor is the reciprocal of an entire
   denominator that is nonzero somewhere. For a finite place this uses
   the nonzero local L-polynomial evaluated at the spectral point and the
   residue cardinality bound `q_v > 1`. Each denominator has finite
   nonnegative order at `1` and its reciprocal has the opposite order.
   Additivity gives nonpositive order for the reinstated factors and for
   the completed function.
4. The two bounds and the negative-order criterion give order `-1` for
   each counted index and order `0` for every other index. By
   `meromorphicOrderAt_fun_prod` the product has order equal to the sum
   of these orders. The sum in `ℤ` is the negative of the cardinality of
   the subtype of counted indices. Its image in `WithTop ℤ` is already
   nonpositive, so taking the minimum with `0` gives the claimed
   `HasPoleOrder`. For an empty family the sum and multiplicity are both
   zero.

For `cuspidalIsobaricPoleOrderReduction`, the split-centre unitarity
theorem supplies the unitary central characters required by the boundary
premise. That premise gives the partial representative for each eligible
set `S` and bounds its order at imaginary part `0`. These witnesses give
`PartialPairNonvanishingAtOne F` at every field, so the shared assembly
applies.

## Provenance

The reduction formalizes the route in §6 of
[`CuspidalIsobaricPoleOrderStatement.md`](CuspidalIsobaricPoleOrderStatement.md).
Getz and Hahn invoke the pair-pole theorem for the isobaric formula.
The fieldwise witness condition isolates the partial-factor order bound
used to rule out cancellation by a zero of a constituent's completed
function. Shahidi's boundary theorem provides that bound in the
two-premise reduction. This implementation uses the symmetry lemma
`CuspidalOperatorRealization.isContragredientOf_symm`, which transposes an
invariant pairing, and the Library theorem
`cuspidalSplitCentreUnitaryCentralCharacter`.

- J. R. Getz and H. Hahn, *An Introduction to Automorphic
  Representations* (2024), (11.23), printed p. 308 (registered PDF p. 319),
  Theorem 11.7.1, printed p. 309 (PDF p. 320), and §11.8 and Lemma 11.8.1,
  printed pp. 311–312 (PDF pp. 322–323).
  Registered source `getz-hahn-2024-automorphic-representations`.
- F. Shahidi, *On Certain L-Functions* (1981), Theorem 5.2, printed
  p. 353 (registered PDF p. 58), for nonvanishing of the partial
  Rankin–Selberg L-function on `Re(s) = 1`. Registered source
  `shahidi-1981-certain-l`.
