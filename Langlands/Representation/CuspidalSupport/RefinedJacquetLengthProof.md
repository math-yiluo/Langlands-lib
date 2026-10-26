# Finite-length detection by refined Jacquet modules: proof

Author: Worker 185. Worker 325's published
`JacquetDetectingFamilyLengthProof` supplies the imported generic
successive-subquotient helpers and the adapted finite-sum length argument;
Worker 325 is credited as a coauthor for that adaptation.

`Langlands.CuspidalSupport.refinedJacquetFiniteLengthDetection.{uF,uV}`
proves the closed published proposition
`Langlands.CuspidalSupport.RefinedJacquetFiniteLengthDetectionStatement.{uF,uV}`.
The field and representation-carrier universes are independent. The target
pair and every existing imported pair are unchanged.

For an actual smooth complex representation `A` of the product Levi
`B.Levi F.Carrier`, the only hypotheses are those of the target: every
quasicuspidal smooth subquotient of `A` is zero, and every proper refined
Jacquet module of `A` has finite length over its actual refined Levi group
algebra. The conclusion is finite length of `A.representation.asModule` over
`MonoidAlgebra ℂ (B.Levi F.Carrier)`.

## Exactness of the actual normalized refined quotient maps

The helper namespace `RefinedJacquetLengthProof` proves:

- `map_toLinearMap`: the linear map of
  `T.normalizedRefinedJacquetMap B C f` is definitionally
  `Representation.Coinvariants.map` for `Jacquet.restrictMap f N`, where
  `N = Geometric.refinedUnipotent F.Carrier B C` is the actual refined
  unipotent subgroup. The carrier is the existing quotient by the span of
  the actual action differences. The action is the existing normalized
  refined action, using `T.refinedLeviInverseHalfModulus B C`; no action or
  quotient is replaced.
- `map_injective`: a smooth middle representation restricts smoothly to
  `N` by `isSmooth_comp` and continuity of the subgroup inclusion.
  `T.refinedUnipotent_finite_containment B C` and
  `coinvariants_map_injective_of_smooth` therefore make the induced map
  injective whenever the original map is injective. The product-Levi
  topological-group instance is installed in this proof.
- `map_exact`: this injectivity, together with
  `coinvariants_map_range_eq_ker` and `coinvariants_map_surjective`, proves
  exactness for the actual normalized refined maps. Only the middle
  representation is assumed smooth. The maps retain their original
  underlying linear maps on restriction, so the original range–kernel
  identity applies directly.
- `length_le`: `IntertwiningMap.equivLinearMapAsModule` turns the injective
  refined map into an injective map over the actual refined Levi group
  algebra. `Module.length_le_of_injective` gives monotonicity of `repLength`.
- `length_step`: apply `map_exact` to the inclusion of nested smooth
  invariant subspaces `S ≤ U` and their actual quotient map. The published
  `repLength_eq_add_of_exact` then gives
  `length J_C(U) = length J_C(S) + length J_C(U/S)`.

Here `lower`, `inclusion`, and `inclusion_exact` are imported unchanged from
`JacquetDetectingFamilyLengthProof`. In particular, `U/S` is the actual
smooth object `SmoothRep.subquotient A U (lower A S U)`, and its witness as
an `IsSubquotient` of `A` uses the identity isomorphism. The imported
`quotient_nontrivial` shows it is nonzero whenever `S < U`.

## A bounded measure on invariant subspaces

`FiniteBlockShapes` proves finiteness of every `BlockShape k`. A refinement
of `B` is a dependent product of such shapes indexed by `Fin B.length`, so
it is finite. The main proof lets `s` be the finite set of all refinements
whose actual refined parabolic is not the top subgroup.

For `C ∈ s`, write `b C = (length J_C(A)).toNat`. The assumed module finite
length, via `Module.length_ne_top_iff`, proves `length J_C(A) ≠ ⊤`; hence
its natural cast equals the original extended natural length. For every
invariant `S`, injectivity of `J_C(S) → J_C(A)` bounds `length J_C(S)` by
`b C`. All lengths used in the sum are consequently finite. Define

`measure(S) = ∑ C ∈ s, (length J_C(S)).toNat`.

Every summand is monotone, and the sum is bounded by `∑ C ∈ s, b C`.
For a strict inclusion `S < U`, let `D = U/S`. If every `J_C(D)` for
`C ∈ s` were zero, the definition of `IsLeviQuasicuspidal` would make
`D` quasicuspidal: the normalized refined carrier is precisely the actual
coinvariant quotient used by that definition. The first hypothesis would
then make `D` a subsingleton, contradicting `quotient_nontrivial`.
Thus some proper `C` has nonzero `J_C(D)`, without any extra detection
premise or chosen witnesses in the theorem's hypotheses.

`repLength_pos_iff` makes this summand's quotient length positive.
Additivity and finiteness give `length J_C(S) < length J_C(U)`;
`ENat.natCast_toNat` transfers the inequality to natural numbers.
`Finset.sum_lt_sum` now proves that `measure` is strictly increasing.

The measure values on a strict chain of length `m` form a natural-number
`LTSeries`. Its `head_add_length_le_nat` inequality bounds `m` by
`∑ C ∈ s, b C`. The published
`LengthCriterionProof.hasCompositionLengthAtMost_of_bound` produces an
actual finite composition series, and `objectCompositionLengthCriterion`
converts this into the required module finite length.

## Scope and provenance

The same proof includes rank zero, empty products, single-block refinements,
zero representations, and an empty set of proper refinements. In the last
case a strict inclusion would produce the forbidden nonzero quasicuspidal
quotient, so no positivity or nonemptiness assumption is needed. The proof
adds no admissibility, finite generation, irreducibility, scalar central
character, finite-dimensional carrier, prior finite length of `A`, or
supplied functor-exactness hypothesis. It uses no general finite-length
induction theorem, `InducedFiniteTypeStatement`, or parent
`GLAdmissibleFiniteLengthStatement`.

The motivating source is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), §2.14(2),
printed p449 / PDF page 10, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
That page was read directly. BZ77 sums Jacquet lengths over standard Levis
associated to an inducing Levi; exactness and detection bound length.
The present all-proper-refinements product-Levi criterion is an internal
derived formulation, not a literal theorem stated in BZ77. Its implemented
proof adapts the published standard-GL length-measure argument, derives
detection from the quasicuspidal-free hypothesis, and proves the refined
exactness needed for the actual quotient/action.
