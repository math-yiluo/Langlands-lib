# Rational Bruhat contractions for smooth affine groups

This internal specialization uses the published theorem
`Langlands.GroupScheme.oppositeCellStatement` from
`Absolute.OppositeCellProof`. The opposite-cell proposition is therefore
discharged in the constructions below.

For a field `k : Type u`, a smooth affine group scheme `G` over `Spec k`,
a commutative group scheme `C`, a homomorphism `i : C → G`, and two
cocharacters `a,b` of `C`,
`Dynamic.smoothAffineOppositeCellOrbitLift` constructs a morphism on
`Spec k × A¹` into the product of the canonical affine representatives of
`U(-(b ≫ i))` and `P(b ≫ i)`. Its inputs are an orbit extension for `a ≫ i`
and the equation that its value at zero is the identity.

The definition specializes the existing `Dynamic.oppositeCellOrbitLift`
to the proved opposite-cell theorem. The equation
`Dynamic.smoothAffineOppositeCellOrbitLift_fac` says that multiplying the
two factors recovers the supplied extension on the whole affine line.
Both the construction and its equation retain the original all-test
dynamic subgroup functors.

`Dynamic.hasProductContraction_of_smooth_affine` unpacks membership in
`U(a ≫ i)(k)` into such an extension, constructs this lift, and applies the
represented-product adapter to its factorization equation. This gives
`Dynamic.HasProductContraction` with factors in the two subgroup functors
on the whole affine-line test scheme.

`hasNormalizerProductContractions_of_smooth_affine` applies that theorem
to a cocharacter and its transform under the torus automorphism induced
by each actual normalizer point. The existing
`groupHom_cocharacterAut_comp` identifies the transformed cocharacter
with conjugation in `G`. No genericity, maximality, splitness of the
commutative source, or connectedness of `G` is needed for this result.

`hasRationalBruhatDecomposition_of_parabolicCovering` combines these
contractions with the published parabolic-covering assembly. It retains
two explicit inputs: equality of the cocharacter centralizer with the
whole-source centralizer as subgroup functors, and covering of actual
rational points by `P(k)N(k)P(k)`. Affineness of the underlying scheme,
needed by that assembly, follows from the affine structure morphism over
the affine field base. The conclusion is the existing
`HasRationalBruhatDecomposition`, including its actual relative-Weyl-group
double-coset indexing.

Finally,
`rationalBruhatStatement_of_centralizer_and_parabolic_inputs` obtains
smoothness and affineness from `IsConnectedReductive` and uses the
published structural covering reduction. It retains exactly four
universal propositions at universe `u`: `GenericCentralizerStatement`,
`GenericMinimalParabolicStatement`,
`ParabolicIntersectionCentralizerStatement`, and
`MinimalParabolicSplitTorusConjugacyStatement`. Its conclusion is the
unchanged `RationalBruhatStatement.{u}`.

No inhabitant of those four propositions is constructed here. This unit
does not prove the unconditional Bruhat statement. All fields, including
finite and imperfect fields, and the trivial-cocharacter and empty-root
cases remain within the quantified scope. The provenance is internal
composition of the named published constructions and proof; no new
external source claim is made.
