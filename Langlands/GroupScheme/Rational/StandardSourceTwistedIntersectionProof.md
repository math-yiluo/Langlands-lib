# Standard source parabolics and radicals for minimum geometric terms: proof

Workers 1239 and 1493. This module proves the published proposition
`Langlands.GroupScheme.StandardSourceTwistedIntersectionStatement` from
`Langlands.GroupScheme.Rational.StandardSourceTwistedIntersectionStatement`.

## Main theorem

`Langlands.GroupScheme.standardSourceTwistedIntersection :
StandardSourceTwistedIntersectionStatement.{u}`.

The type is exactly the published statement at its universe `u`, with no further
hypotheses. So for every field `k : Type u`, connected reductive `G` over `Spec k`,
maximal split torus inclusion `i`, generic cocharacter `ν` and every
`IsRelativeWeylCoxeterRealization` of the scheme relative Weyl quotient, the
following holds. For finite simple-root subsets `I, J`, every minimum
representative `w` of `W_I w W_J` and every scheme-normalizer lift `n` of `w`,
put `K = intersectionSubset cs I J w`. Then

`L_J ⊓ comap (G.innerIso n).hom P_I = L_J ⊓ P_K`,

`L_J ⊓ comap (G.innerIso n).hom U_I = L_J ⊓ U_K`,

as equalities of subgroup functors, i.e. on every test scheme over `Spec k`,
including nonreduced ones. Here `P`, `L` and `U` are the literal published standard
parabolic, Levi and unipotent subgroup functors. No splitness of `G`, perfectness,
characteristic assumption, root reducedness or nonempty simple-root type is added.

## Proof

The proof is a single application of the published conditional assembly
`standardSourceTwistedIntersectionStatement_of_negation_of_signs`
(module `Rational.StandardSourceTwistedIntersectionReduction`). That theorem derives
the target from two structural statements. Both are now proved without extra
premises:

- `relativeRootNegation : RelativeRootNegationStatement.{u}`
  (module `Rational.RelativeRootNegationProof`): the actual relative roots of a
  maximal split torus of a connected reductive group are stable under negation.
- `relativeRootSignsDetermineDynamic : RelativeRootSignsDetermineDynamicStatement.{u}`
  (module `Rational.RelativeRootSignsProof`): two cocharacters with the same
  nonnegative, zero and positive pairings on every actual relative root have the
  same dynamic parabolic, centralizer and unipotent subgroup functors on all test
  schemes.

## How the assembly works

The conditional assembly is proved in `Rational.StandardSourceTwistedIntersectionReduction`.
Its steps, as implemented there, are:

1. It obtains affineness, smoothness, the monomorphism property of `i` and the
   finiteness of the simple roots from the hypotheses.
2. `IsRelativeWeylCoxeterRealization.isStandardSourceTwistedIntersection`
   reduces the target to one property on each finite face `K`: any two
   `K`-standard cocharacters have the same dynamic subgroup functors.
   For this it proves the inclusions `L_J ⊓ P_K ≤ L_J ⊓ comap Int(n) P_I` and
   `L_J ⊓ U_K ≤ L_J ⊓ comap Int(n) U_I` without further assumptions. The proof
   transports an `I`-standard cocharacter along the inverse of `n` and adds a
   large multiple of a `J`-standard cocharacter, which centralizes `L_J`. This
   gives a `K`-standard cocharacter with the same orbit behaviour on `L_J`.
   The comparison on `K` then gives the reverse inclusions.
3. Two `K`-standard cocharacters have the same relative-root signs by
   `IsStandardCocharacter.haveSameRelativeRootSigns`. This lemma uses negation
   stability, here supplied by `relativeRootNegation`.
4. `relativeRootSignsDetermineDynamic` turns equal signs into equality of the
   dynamic parabolic, centralizer and unipotent subgroup functors. This is the
   comparison step 2 needs.

## Dependencies

- `Langlands.GroupScheme.standardSourceTwistedIntersectionStatement_of_negation_of_signs`
- `Langlands.GroupScheme.relativeRootNegation`
- `Langlands.GroupScheme.relativeRootSignsDetermineDynamic`

## Provenance

This is an internal structural target. It has no single literature source. The
proof is internal: it composes the three published Library results above, and
their own Markdown files give their routes and sources.
