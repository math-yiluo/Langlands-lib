# Conditional Jacquet assembly for the actual rational-point family

`rationalJacquetGeometricSum` constructs the signed sum of actual geometric
intersection maps after ambient normalized Jacquet restriction. It is
`jacquetGeometricSum` specialized to the literal rational-point families,
at the canonical finite enumeration of the actual simple roots. Each row
uses the literal minimality indices `J,I`, every supplied lift, and the
original coefficient `(-1 : ℤ) ^ I.card`.

`rationalJacquetCompatibility_of_geometricExpansion` specializes the
conditional `jacquetCompatibility_of_geometricExpansion` theorem to the
literal rational-point families in the published
`RationalJacquetCompatibilityStatement`. It is a helper, not a proof of
that whole proposition: it explicitly requires an actual geometric
expansion and the named common-term and longest-term comparisons.

The helper uses a field with the displayed topological and functor data;
in particular it applies to every nonarchimedean local field in the target.
The group is the actual rational-point group of a connected reductive group
scheme, with canonical evaluation topology `pointTopology`, its actual maximal split torus, and
a generic cocharacter. The helper takes the affine and monomorphism
instances explicitly;
connected reductivity and maximal splitness derive them in the target.
The labels are the actual `SimpleRoot i ν`, with finite enumeration supplied
by `simpleRelativeRootFintype` from `HasRelativeRootSystem`. This derived
instance is bound by `letI` in each declaration type before the Weyl and
associated-subset data, matching the target. The Weyl group is the quotient of the actual torus normalizer by its full centralizer.
Independent universes `u,v` give representation carriers
`max (u + 1) v`, including positive characteristic, nonsplit groups,
empty root sets and all standard subsets.

Ambient decompositions use
`isSemidirectDecomposition_of_standardCocharacterStatement`, and
`standardParabolicFiniteLength` derives the required exactness from the
displayed topological, projection and compact-subgroup-limit premises
and the two finite-length preservation inputs. Inside the associated
closed Levi, `isSemidirectDecomposition_in_levi` uses
`StandardLeviIntersectionStatement`, and
`standardLeviParabolicFiniteLength` supplies exactness at the same
carrier universe. The helper needs restricted premises only at the
selected associated Levi; the whole target supplies them for every Levi.
All inside-Levi subgroups are the literal `subgroupOf` restrictions.

The associated subset remains exactly `associatedSubset cs J`.
`associatedLeviConjugation_of_standard` derives its actual subgroup
image from `StandardLeviConjugationStatement`, the displayed actual
normalizer and full-centralizer comparisons, root-length and positive
simple-reflection comparisons, minimality criterion and associated-subset
laws. `conjugationMembership_of_map_eq` gives exactly the membership
witness used by the target's `conjugationK0`. The theorem allows every
actual normalizer lift of `longestRep cs J` and uses its actual conjugating
element. No equality of lifts or assumed K0 conjugacy law is substituted.

The proof is the generic assembly at universes
`uI = uG = u`, `uV = max (u + 1) v`; the rational operators unfold to its
actual operators. Consequently the conclusion is exactly
`rJ.comp D = C.comp (DLprime.comp rJprime)`, with original integer signs.
No new normalization or rank sign occurs.

The extra inputs remain obligations:
`GeometricIntersectionDecompositions` and `GeometricTermFiniteLength`
construct the actual intersection terms;
`GeometricK0ExpansionStatement` supplies their representation identity;
the family `F` and `JacquetGeometricTermReduction` factor those terms
through their simple-image intersections;
`JacquetLongestTermReduction` identifies the survivor with the actual
transported restricted-Levi term. This module proves none of those inputs,
and does not add them to `RationalJacquetCompatibilityStatement`.

Provenance is an internal actual-family specialization of
`JacquetK0Assembly`, motivated by Aubert 1995 Theorem 1.7(2) and (1.9),
printed pp.2181–2183. The sum constructor directly invokes
`jacquetGeometricSum`; the conditional proof directly invokes only
`jacquetCompatibility_of_geometricExpansion`; its elaborated data use
the exact constructors and adapters named above. The generic helper's
Markdown describes its proof-body dependencies and the separate
geometric-lemma premise. No Langlands classification, character
independence, adjointness, cuspidal-support, Proposition 3.2 or original
Theorem 3.6 proof is invoked here.
