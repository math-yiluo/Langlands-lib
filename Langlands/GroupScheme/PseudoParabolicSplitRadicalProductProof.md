# The split-radical product description of pseudo-parabolics

`Langlands.GroupScheme.pseudoParabolicSplitRadicalProduct.{u}` proves exactly
`PseudoParabolicSplitRadicalProductStatement.{u}`. For every smooth connected
affine group scheme over every field, supplied ordinary and split ground-field
unipotent radicals, and cocharacter, the two ordered fppf-local products with
the dynamic parabolic agree on every relative scheme test. The published
statement and its imported definitions are unchanged. The theorem has no
additional premise.

The proof constructs the canonical inclusion `m : V ⟶ U` between the supplied
split and ordinary radical representatives using
`IsSplitUnipotentRadical.inclusionInRadical`. Its composite with the supplied
ordinary radical inclusion `j` is the supplied split radical inclusion `n`.
The radical predicates provide smoothness of `U` and `V`.
`exists_quotient_inRadical` provides an actual smooth connected affine quotient
`q : U ⟶ Q`, with the full all-relative-test kernel equal to the image of `m`.
The affineness needed for this quotient construction comes from the original
affine ambient group and the closed radical inclusions.

The published theorem `splitRadicalWoundQuotient` applies to these exact
representatives, the commuting inclusion and this quotient. It supplies
`HasConstantAffineLineMaps Q`: every affine-line scheme morphism into `Q` is
constant at a rational value. Woundness is proved by that imported theorem;
it is not an additional hypothesis of the product theorem.

The quotient-action theorem
`fppfLocallyInProduct_parabolic_of_wound_quotient` now shows that every point of
the ordinary radical belongs fppf-locally to the ordered product of the dynamic
parabolic and the split radical. Its geometric hypotheses come from the
ambient group, the radical predicates and the quotient just constructed.
Its normality hypotheses are the original all-test normality of the two
ambient radical images. Internally this published theorem restricts
cocharacter conjugation to the ordinary radical, descends it to the quotient,
uses woundness to make the split-torus action trivial, and applies the smooth
semigroup-quotient image and full-kernel factorization constructions. The
result supplies actual local factors without assuming lifts or local sections.

Finally `FppfLocallyContainedInProduct.product_iff` substitutes this local
factorization for the ordinary radical factor of an arbitrary product. That
published theorem composes the witnessing fppf covers and combines the two
parabolic factors in their given order. The reverse implication uses
`IsSplitUnipotentRadical.range_le_unipotentRadical`, so it only enlarges the
right subgroup. The resulting equivalence is the exact target for the original
relative test `T` and point `x`.

All constructions retain arbitrary universe `u`, every field including finite
and imperfect fields and every characteristic, and the original supplied group
schemes and cocharacter. Tests include nonaffine and nonreduced schemes. No
reductivity, perfectness, infinitude, theorem-valued premise, lift or local
section is added.

This is an internal proof assembly of the published target corresponding to
the first equality in CGP Proposition 2.2.4. The target's paired Markdown
records the original-source provenance. The implementation uses the published
wound-quotient, quotient-action and fppf-cover composition results rather than
repeating their proofs. Worker 1468 authored the final assembly and cover
composition infrastructure; Worker 1150 contributed the quotient-action and
kernel-product infrastructure and the proof architecture. The wound-quotient
proof is imported from the published Library.
