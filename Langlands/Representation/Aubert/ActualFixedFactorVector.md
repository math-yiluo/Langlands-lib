# Actual irreducible images from a fixed composition-factor vector

Authors: Worker 585 (actual subquotient and realization adapters), with
Worker 76 (the fixed-vector strategy and the reused integral counting proof).

This internal module joins the published actual composition-factor
construction, `IrreducibleImageAssembly`, and `EffectiveFixedVector`. It
works over an arbitrary field and topological group, with independent field,
group and common representation-carrier universes. Every Grothendieck class
uses the existing exact finite-length quotient, including all actual
nonsplit short exact relations.

`factorSubquotient A s i` forms the actual smooth quotient of the upper
filtration step by the lower step pulled back into it. Its action is the
existing graded action; `factorSubquotientEquiv` is the identity equivalence
of those actions. The object is an actual `SmoothRep.IsSubquotient` of `A`.
This is the arbitrary-field version of the same quotient construction
appearing in `CuspidalSupport.filtrationSubquotient`; the proof uses the
generic filtration and quotient definitions directly.

`mem_support_compositionFactors_iff_isSubquotient` identifies support of the
canonical factor vector with actual irreducible subquotients. For support
implying subquotient, the coordinate is the natural number of equivalent
graded factors in the chosen actual composition series. A nonzero coordinate
makes that finite subtype nonempty. A witnessing graded factor and its
actual quotient realize the subquotient. In the reverse direction, the
published `simpleSubquotientFactor` puts an actual irreducible subquotient
into the chosen series. It supplies a member of the counting subtype, so the
natural count and its integer coordinate are positive. No semisimplicity or
finite vector-space dimension enters either implication.

`generator_image_of_effective_fixed_class` assumes an injective exact-K0
endomorphism `D`, an actual finite-length object `M` whose class is fixed by
`D`, and effectivity of the `D`-image of every actual irreducible subquotient
of `M`. It concludes that the transported image of every label supported in
the factor vector of `M` is a single generator. The factor vector is
effective by actual natural-valued multiplicities. The published transport
identities transfer injectivity and the fixed-class equality. The preceding
support characterization converts the actual effectivity hypothesis into
the supported-generator hypothesis of
`VirtualRepresentation.generator_image_of_effective_fixed`, which proves
the conclusion by positive integral counting.

`exists_irreducible_image_of_effective_fixed_class` permits a sign
`s = 1` or `s = -1`. It assumes injectivity of the original `D`, that
`s • D` fixes the actual class of `M`, and effectivity of the signed images
of its actual irreducible subquotients. Multiplication by either permitted
sign preserves injectivity. The counting result produces a generator for
the signed image of a supplied actual irreducible subquotient `A`.
The published signed-generator realization adapter selects an actual
irreducible representative `B` and removes the sign, giving
`D[A] = [B]` or `D[A] = -[B]`. Both finite-length witnesses follow from
irreducibility. The embedding version uses the published positive
composition-multiplicity result for an actual injective intertwiner to
place `A` in the same support.

The provenance is internal algebra derived from the cited published Lean
constructions and proofs. This module supplies conditional assembly, not
signed effectivity for the Aubert operator, a corrected duality complex, or
the unconditional all-rank irreducible-image theorem. Its hypotheses are
explicit here and are not added to that theorem's target. It imports no
segment, multisegment, strong-head, tempered, square-integrable or regular
classification result and changes no published target or dependency pair.
