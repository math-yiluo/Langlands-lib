# Upper cuspidal quotients of irreducible admissible product-Levi representations

Author: Worker 196.

`Langlands.CuspidalSupport.leviCuspidalQuotientTheorem` proves exactly
`Langlands.CuspidalSupport.LeviCuspidalQuotientStatement.{uF,uV}` from
[`LeviCuspidalQuotientStatement`](LeviCuspidalQuotientStatement.md).
The field universe `uF` and input carrier universe `uV` are independent.
The only representation hypotheses are the irreducibility and admissibility
already in that proposition.

For the supplied topology `T.topology`, a positive rank, a block shape `D`,
and an irreducible admissible `σ` of the actual product Levi
`D.Levi F.Carrier`, the theorem supplies a refinement `R`, an irreducible
cuspidal `ω` of `(D.flatten R).Levi F.Carrier`, and a surjective intertwiner
from the exact normalized upper induction requested by the statement to
`σ.ρ`. The carrier of `ω` lies in `max uF uV`, while the target keeps the
original carrier of `σ` in `uV`. The conclusion includes the exact
`RelativeJacquetMultiplicity.fineTwist T D R ω 0 0`.

## Implemented proof

The new auxiliary declarations are in
`Langlands.CuspidalSupport.QuotientAssembly`; compact-open cofinality is
reused from the existing p-adic Library theorem.

1. `Langlands.PadicField.TopologicalData.leviCompactOpenCofinal` from
   [`Shahidi/IntertwiningPadic`](../Shahidi/IntertwiningPadic.md) supplies,
   inside every open subgroup of an actual product Levi, a compact open
   subgroup using `T.leviCompactOpen`.
   `leviSmoothDual_isIrreducible` applies the published smooth-dual
   irreducibility criterion with compact-open separation and admissible
   bidual reflexivity. Thus the smooth dual of `σ` is irreducible.
2. `liftedSmoothDual` lifts this smooth dual to carrier universe
   `max uF uV`, using `universeLiftRepresentation`.
   `liftedSmoothDual_isIrreducible` proves irreducibility of that lift by
   `isIrreducible_universeLift_iff`; smoothness follows from
   `isSmooth_universeLift_iff`.
3. Apply the published
   `CuspidalSupport.normalizedRefinedQuasicuspidalEmbedding` at carrier
   universe `max uF uV` to `liftedSmoothDual`. It gives an actual refinement
   `R`, an irreducible smooth quasicuspidal `τ` of the flattened Levi, and an
   injective intertwiner from the lifted dual into
   `T.normalizedRefinedInduced D R
   (τ.representation.comp e.symm.toMonoidHom)`, where
   `e := flattenedLeviEquiv F.Carrier D R`.
4. In `quotient_of_quasicuspidal_lifted_embedding`, the published
   `LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility` makes `τ`
   admissible. Together with its quasicuspidality, this is
   `IsLeviCuspidal (D.flatten R) τ.representation`.
   The published `leviCuspidalContragredient` gives cuspidality of its
   smooth dual. Precompose the embedding with the actual injective
   `universeLiftEquiv` from the original smooth dual into its lift.
5. `quotient_of_dual_embedding` sets
   `ω := Rep.of (smoothContragredient τ.representation)`.
   Its irreducibility follows from step 1 on the flattened Levi, and its
   cuspidality was obtained in step 4. It constructs the actual quotient
   map by the equivalences and smooth dual map described below.
6. `fineTwist_zero` proves that the real exponent function
   `fun k => -0 + 0` is zero, then rewrites with
   `T.leviRealPowerTwist_zero`. This identifies the requested fine twist
   with `ω.ρ.comp e.symm.toMonoidHom`. Rewriting the induction's input
   gives the exact requested source for the quotient map.

The final theorem applies these constructions and returns `R`, `ω`, their
proved properties, and the surjective map. The helpers' explicit embedding
and dual-cuspidality arguments are discharged by the published theorems in
steps 3 and 4; they are no extra hypotheses on the final theorem.

## The quotient map and the normalizations

Write `a := e.symm.toMonoidHom` and
`τ' := Rep.of (τ.representation.comp a)`. The published
`Parabolic.isAdmissible_flattenedLeviTransport_iff` proves admissibility of
`τ'` from that of `τ`. The refined clause of
`Parabolic.naturalNormalizedInductionDuality` supplies an actual
representation equivalence

```
E : smoothContragredient (T.normalizedRefinedInduced D R τ'.ρ)
      ≃ T.normalizedRefinedInduced D R (smoothContragredient τ'.ρ).
```

Here and below `≃` denotes the appropriate representation equivalence.
`smoothDualPullbackEquiv` identifies
`smoothContragredient (τ.representation.comp a)` with
`(smoothContragredient τ.representation).comp a`. It retains each
underlying linear functional. Its two membership proofs use
`isSmoothVector_dual_comp_continuousMulEquiv_iff` with
`(flattenedLeviEquivContinuous F.Carrier D R).symm`; the intertwining
identity uses preservation of inversion.

`refinedInducedEquiv` transports this equivalence through the actual
refined induction: inflate along `refinedLeviProjection`, apply the common
positive half-modulus twist with `twistEquiv`, then apply
`Induction.smoothInducedEquiv`, which postcomposes smooth functions
pointwise. Call the resulting equivalence `P`. Its direction is from
induction of the smooth dual of `τ'` to induction of `ω.ρ.comp a`.

The canonical smooth-bidual map of `σ` is bijective:
`smoothBidual_injective_of_compact_cofinal` gives injectivity, and
`smoothBidual_surjective_of_compact_cofinal` gives surjectivity using the
given admissibility. Let `B` be its representation equivalence. If `j`
is the embedding of the unlifted smooth dual obtained in step 4, the
constructed quotient is the composition

```
I(ω ∘ a) --P⁻¹--> I((τ')~) --E⁻¹--> I(τ')~
         --contragredientMap j--> σ~~ --B⁻¹--> σ.
```

The smooth dual map is surjective by
`contragredientMap_surjective_of_injective_of_compact_cofinal`, applied to
the actual injective `j`. The target of `j` is smooth by
`T.isSmooth_normalizedRefinedInduced`, and the source of `j` is smooth by
`isSmooth_smoothContragredient`. All other arrows are inverse
representation equivalences and therefore surjective. The proof composes
these surjectivity statements for the displayed actual intertwining map.

Every induction here is the supplied normalized upper refined induction
inside `D.Levi F.Carrier`, with covariance
`f(x g) = δ^(1/2)(x) τ'(m(x))(f(g))` and right translation. The duality
used is the proved same-parabolic induction duality, whose refined clause
is instantiated at `uV := max uF uV`. The quotient construction introduces
no change of parabolic or sign. The internal opposite/upper comparison
needed for cuspidality of the dual datum is already proved in
[`LeviCuspidalContragredientProof`](LeviCuspidalContragredientProof.md).

## Universes and boundary cases

The smooth dual of the original input has carrier universe `uV`.
Lifting it before the embedding places both the embedding input and the
resulting `τ` in `max uF uV`. Consequently the smooth dual datum `ω` and
all induced sources have carrier universe `max uF uV`. Precomposition with
`universeLiftEquiv` removes the input lift by an actual intertwiner, and
the bidual inverse ends in the original carrier of `σ`. No universe
lowering or equality between carriers in different universes is assumed.

The statement asks only for positive ambient rank. The proof does not use
the positivity hypothesis and makes no properness assumption on `R`;
whole-product refinements remain allowed. All helper theorems used on the
flattened shape include their corresponding boundary cases.

## Provenance and dependency scope

This is a derived proof assembled from the named published Library results.
The target's literature motivation and its distinction from an
opposite-parabolic embedding are described in
[`LeviCuspidalQuotientStatement`](LeviCuspidalQuotientStatement.md).
The implemented route takes the normalized upper embedding from
[`RefinedQuasicuspidalEmbeddingProof`](RefinedQuasicuspidalEmbeddingProof.md)
and uses the established smooth-dual and induction-duality constructions.
It does not assert that the target is a literal transcription of a
printed theorem.

The proof uses irreducible quasicuspidal Levi admissibility; it needs no
admissibility theorem for arbitrary irreducible Levi representations.
It uses no tensor factorization. The zero twist is the named statement's
normalization, with no positivity assertion on real parameters.

The module's complete project import closure was audited for the excluded
classification and exhaustion inputs. Traversing its `Langlands.*` imports
recursively, counting each module once and including this proof module,
gives 271 project modules at Library commit `b22e1857`, with no missing
project imports. The classification modules are recorded below.
Proposition definitions imported by the target, including the relative
multiplicity statement, remain definitions and supply no proof input to
this construction.
The unrestricted form of Silberger 1978 Lemma 5.3 is not used.


The classification modules in that closure are `CanonicalConstituents`,
`ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`,
`RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`, and
`SupercuspidalTwist`. These contain basic constructions, transport lemmas,
and statement definitions. In particular, `Segments` does not import or
prove the ordered-segment classification. The generic head constructions
in `CanonicalConstituents` assert no regular Langlands head theorem.
No module or declaration of the excluded positive-root support, joint
support, regular Langlands head or exhaustion, tempered exhaustion,
square-integrable Langlands classification, or ordered-segment
classification occurs in this import closure. The sole incidental
exhaustion declaration is the Prop-valued `UnipotentExhaustionClause`
about unipotent subgroups. The imported relative multiplicity module
mentions Lemma 5.3 in its source description, but only its actual
`fineTwist` and `innerInduced` definitions are used here.

A development Lake build and declaration inspection succeeded with zero
diagnostics. Inspection reported the independent level parameters `uF`
and `uV`, and only `propext`, `Classical.choice`, and `Quot.sound` as
axioms. Development checks do not establish independent semantic
acceptance or publication.
