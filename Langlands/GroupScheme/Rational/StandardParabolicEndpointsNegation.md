# The endpoints of standard parabolics from negation stability of relative roots

Author: Worker 293.

This module reduces `StandardParabolicEndpointsStatement` to one premise,
`RelativeRootNegationStatement`. That statement says the actual relative roots of a
maximal split torus in a connected reductive group are stable under negation. The
module does not prove that premise, and it is not an unconditional proof of the
endpoint target. Every statement here is at universe `u`. Every subgroup-functor
equality holds on all test schemes, because it is an equality of the published
`SubgroupFunctor` values.

## Definition

`StandardSubgroupsDynamic i ν` is a property of a torus inclusion `i : T.toGrp ⟶ G`
(with `G` affine over `Spec k`) and a cocharacter `ν` of `T`. It says: for every set
`J` of characters of `T` and every cocharacter `ζ` that is standard for `J` relative to
`ν` (`IsStandardCocharacter i ν J ζ`), the three standard subgroup functors
`standardParabolic i ν J`, `standardLevi i ν J` and `standardUnipotent i ν J` equal the
dynamic parabolic, centralizer and unipotent subgroup functors of `ζ` composed with
`i`. It does not say that a standard cocharacter exists for any `J`. It quantifies over
all sets `J`. Restricted to faces `J ⊆ simpleRelativeRoots i ν`, it is the comparison
half (the second conjunct) of the conclusion of `StandardCocharacterStatement` for `i`
and `ν`. For a single `J`, the published property
`StandardCocharacterDynamicComparison i ν J` implies the same three equalities, by
`StandardCocharacterDynamicComparison.standard_eq_dynamic`. This definition is internal
to the Library, not taken from the literature: it names the conclusion of the comparison
theorem below.

## Declarations

- `relativeRootNegationStatement_of_relativeRootReflectionExistence`: if every connected
  reductive group with a maximal split torus has a `RelativeRootReflectionData`
  (`RelativeRootReflectionExistenceStatement`), then the relative roots are stable under
  negation. Fix the data `D` from the premise. The published lemma
  `RelativeRootReflectionData.neg_mem_relativeRoots` (`Rational.ReflectionNegation`)
  shows that `-α` is a root for every root `α`. The extra centralizing condition in the
  premise is not used.
- `standard_eq_dynamic_of_relativeRootNegation`: take a connected reductive `G`, a maximal
  split torus `i` and a generic cocharacter `ν`. Assume `RelativeRootNegationStatement`.
  Then `StandardSubgroupsDynamic i ν` holds. So for any index set `J` and any cocharacter
  `ζ` that is standard for `J`, `standardParabolic i ν J`, `standardLevi i ν J` and
  `standardUnipotent i ν J` equal the dynamic parabolic, centralizer and unipotent
  subgroup functors of `ζ` composed with `i`.
  This is the comparison half of `StandardCocharacterStatement`. The existence half
  (some standard cocharacter exists for every face) is neither asserted nor used.
- `standardParabolic_simple_eq_top_of_relativeRootNegation`: under the same premise, the
  standard parabolic for the full simple-root index `simpleRelativeRoots i ν` is `⊤`.
- `standardParabolicEndpoints_of_relativeRootNegation`: the premise implies all five
  clauses of `StandardParabolicEndpointsStatement`.
- `standardParabolicEndpoints_of_relativeRootReflectionExistence`: the same conclusion
  from `RelativeRootReflectionExistenceStatement`, through the first declaration.

## Proofs

**Comparison.** Take two cocharacters `ξ` and `η` that are standard for the same `J`.
The published lemma `IsStandardCocharacter.haveSameRelativeRootSigns`
(`Rational.PositiveRootInduction`) needs genericity of `ν` and negation stability of the
roots of `i`. Given these, `ξ` and `η` have the same weak, zero and strict signs on every
actual relative root. Here is why. Induction on the positive integer pairing with `ν`
writes each positive root as a sum of simple roots. So the signs of a standard
cocharacter on positive roots are fixed by `J`. Genericity means every other root has
negative pairing with `ν`, and negation turns it into a positive root. The published
theorem `relativeRootSignsDetermineDynamic` (`Rational.RelativeRootSignsProof`) proves
`RelativeRootSignsDetermineDynamicStatement`. It turns equal signs into equal dynamic
parabolic, centralizer and unipotent subgroup functors. That is
`StandardCocharacterDynamicComparison i ν J`. The published lemma
`StandardCocharacterDynamicComparison.standard_eq_dynamic`
(`Rational.StandardCocharacterReduction`) then identifies each standard subgroup
functor, which is an intersection over all standard cocharacters for `J`, with the
dynamic subgroup functor of any one of them.

**Endpoints.** Apply the comparison to two cocharacters. For the empty index, use `ν`
itself (`isStandardCocharacter_empty_self`). For the full simple-root index, use `0`
(`isStandardCocharacter_simple_zero`). Both lemmas come from `Rational.EndpointReductions`.

1. The empty-index parabolic equals the dynamic parabolic of `ν`, by the comparison
   at `ν`.
2. The empty-index Levi equals the whole-torus centralizer. The published
   `genericCentralizer` (`Rational.GenericCentralizerProof`) identifies the dynamic
   centralizer of `ν` with `torusCentralizer i`. Then
   `standardLevi_empty_of_genericCentralizer` applies.
3. and 4. At the full index the comparison at `0` gives the dynamic parabolic and
   centralizer of the zero cocharacter. These are `⊤`, by
   `groupHom_zero_comp_eq_trivialCocharacter` and the `@[simp]` lemmas
   `Dynamic.parabolic_trivialCocharacter` and `Dynamic.centralizer_trivialCocharacter`.
   The ⊤ lemma for the parabolic alone is proved the same way.
5. The full-index unipotent is `⊥`, by `standardUnipotent_simple_eq_bot`. That lemma
   needs no premise.

## Provenance

This is a derived reduction. It combines published definitions and theorems of the
Library and adds no assertion from the literature. In the classical theory the relative
roots of a connected reductive group form a (possibly nonreduced) root system, so they are
stable under negation. Here that property stays an explicit hypothesis.
