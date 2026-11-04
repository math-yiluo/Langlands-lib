# Rational principal-open comparison and actual conjugation on exact K0

This internal derived adapter composes the actual rational principal-open trace
comparison with the genuine induction-conjugation identity. The field and
coefficient universes are independent. It uses the canonical rational-point
topology and literal `SimpleRoot i ν` labels over every nonarchimedean local
field. No characteristic-zero, splitness or nonempty-root restriction is added.

The two actual decompositions have Levis `L_I = levi i ν I` and
`L_J = levi i ν J`. Their parabolics need not be the named standard ones.
The point `g` has the literal membership witness
`hIJ : ∀ x, x ∈ L_J ↔ g⁻¹ * x * g ∈ L_I`. Every point with this witness is
allowed, including every actual normalizer lift used by the rational target.
The ambient canonical rational-point group is locally compact,
nonarchimedean and Hausdorff with its Borel measurable structure; the measure
is regular Haar. Both original radicals are closed, both original Levi
projections continuous and both original actual left quotients compact.

`rationalConjugateInductionComparisonLocus` is the actual set of unramified
characters of the full rational norm family on `L_J` where two genuine
normalized induced distributions agree. The first uses `hJ`; the second uses
`hI.conjugateWithLevi g hIJ`, hence the actual conjugate parabolic `g P g⁻¹`
and the literal common Levi `L_J`. The coefficient is any admissible smooth
`L_J` representation. The induced admissibility needed to define both genuine
trace distributions is derived from those data.

The definition installs `compactSpace_leftQuotient_conjugateSubgroup` locally
to derive compactness of the conjugate quotient from that of the original
quotient. This theorem uses the actual inverse-conjugation quotient
homeomorphism. Closedness of the conjugate radical follows from
`isClosed_conjugateSubgroup`, and
`IsSemidirectDecomposition.continuous_conjugateWithLevi_projection` derives
continuity of the actual conjugate projection from the original projection.
There is no extra topology assumption on a conjugated object.

`inductionK0_comp_conjugationK0_of_rationalPrincipalOpen` concludes equality of
the whole integer-linear maps
`i_J.comp (conjugationK0 g hIJ) = i_I` on the genuine exact finite-length
Grothendieck group. The transported action is inverse-conjugation pullback,
`x ↦ σ(g⁻¹*x*g)`, with exactly the displayed direction of `hIJ`.

In addition to the preceding data, the theorem takes closedness of the two
original parabolics, preservation of finite length and finite-length short
exactness by their two actual induction functors, connected reductivity of
exactly `Standard.leviScheme i ν (rootSet i ν J)`, and admissibility of every
finite-length ambient and `L_J` representation at carrier universe `max u v`.
For every actual finite-length coefficient of `L_J`, its comparison input
supplies a nonzero polynomial in the actual finite unramified coordinates
whose principal open lies in the defined comparison locus. The polynomial may
depend on the coefficient object. Rank zero is included.

The implemented proof applies the published
`inductionK0_comp_conjugationK0_of_sameLevi`. Its remaining map equality is
supplied by `rationalLeviInductionK0_eq_of_principalOpen` for `hJ` and the
actual conjugated `hI`. The published
`conjugateInductionFunctor_preservesFiniteLength` and
`conjugateInductionFunctor_preservesShortExact` derive both preservation
properties of the conjugated induction, and the topology laws above supply
its closedness, continuous projection and compact quotient. Each specified
principal open is contained in the actual comparison locus, so it provides
exactly the distribution equality required by the same-Levi map theorem.
There is no assumed isomorphism between different same-Levi inductions.

The character step uses `Character.exactK0CharacterRealization` and
`Character.exactK0CharacterInjectivity`, hence
`Character.distributionShortExactAdditivity`,
`Character.finiteFamilyLinearIndependence` and
`SmoothRep.irreducibleGrothendieckStatement`, as documented in
`RationalLeviInductionK0Comparison.md`. The conjugation step uses the actual
`inductionConjugationIso` and elementary invariant-subspace transport,
as documented in `ConjugateInduction.md`; the relevant transport declarations
are `pullbackFunctor_preservesFiniteLength`,
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`,
`length_comp_surjective` and
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`.
No new classification, geometric-lemma, adjointness or cuspidal-support theorem
is supplied by this composition.

Connected reductivity of the same actual Levi, finite-length admissibility,
the genuine generic comparison and its nonzero polynomial witness remain
explicit inputs. This is an intermediate conditional reduction, not a proof
of the whole `RationalInducedK0WeylConjugacyStatement`.

The 6 local instances have module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
