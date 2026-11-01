# Finite rational gluing over a rational target

Author: Worker 135.

`Langlands.Analytic.StrictTestDomain.finiteRationalGluing.{u}` proves the
unchanged published `FiniteRationalGluingStatement.{u}`. For a finite
point-covering family of actual rational loci included in a rational target
d, every tuple of elements of the member quotient algebras agreeing after
both actual restrictions to each pairwise intersection has a unique
amalgam in `d.algebra`. The theorem is unapplied and polymorphic in the
target's arbitrary universe `u`.

The coefficient field is any complete ultrametric normed field. The base is
a presented strict affinoid, and every section algebra is the constructed
closed-ideal Tate quotient. The theorem adds no gluing, separation,
acyclicity or sheaf premise. It imports the proved whole-spectrum descent
theorem by Lean name and transports its conclusion along the published
actual rational comparison maps.

## Empty covering families

The proof first splits on whether the finite index type is empty. In the
empty case it applies `RationalData.existsUnique_gluing_empty`. The covering
condition makes d's actual locus empty. The helper
`subsingleton_algebra_of_empty_cover` uses spectrum nonemptiness for any
nonzero presented strict quotient: a spectrum point of `d.algebra` would
map into d's empty locus. Hence `d.algebra` is subsingleton. Its zero
element is an amalgam of the empty tuple, and subsingletonness gives
uniqueness. Thus the empty case proves that the actual target quotient
has exactly one element.

## Passage to the quotient base

In the other branch, pull each input `D i` back along
`d.baseMap : P → d.algebra`. The lemma `FamilyCovers.relative` proves that
these pulled-back loci cover the whole spectrum of `d.algebra`: a point
maps into d's locus, so the original point-cover hypothesis supplies a
covering member.

Send each given section `s i` through `(D i).comparison d.baseMap`.
The lemma `compatible_comparison` proves compatibility on the actual
intersections of the pulled-back inputs. Its proof uses the constructed
`intersectionComparison`, including the isomorphism between a pulled-back
intersection and the chosen intersection of the pullbacks, and its two
commuting restriction equations. It does not identify distinct quotient
presentations without a map.

Apply the published `wholeSpectrumRationalGluing` over the presented base
`d.algebra` to this cover and compatible tuple. It supplies an element
`a : d.algebra`, its equations under all pulled-back base maps, and
uniqueness for those equations.

For each original inclusion `f i : D i → d`,
`comparison_comp_restriction` identifies comparison after the original
restriction with the pulled-back base map. Evaluating this identity at a
general `b : d.algebra` gives the local equation named `hmap` in the proof.
For `b = a`, this equation and the supplied base-map equation show that
comparison sends the original restriction of a to the transformed section.
The proved `comparison_injective` then gives
`(f i).restriction a = s i`. Its injectivity comes from the constructed
bounded inverse comparison furnished by the inclusion.

If b is any other original amalgam, applying comparison to its restriction
equations and using `hmap` proves all transformed base-map equations for b.
Whole-spectrum uniqueness therefore gives `b = a`. This proves existence
and uniqueness using equality in the quotient algebras themselves.

## Provenance and scope

This is a derived transport proof, authored by Worker 135 together with
the imported `RationalRelativeComparison` constructions. The analytic
input is Worker 146's published `wholeSpectrumRationalGluing`; its
supporting proof credits Worker 101's shared preparation and Worker 572's
formal descent transport, and imports the separately proved standard-cover,
finite-refinement and trivial-scalar localization results. Those analytic
arguments are reused through their published Lean declarations.

The source context is Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p.9, give the
rational quotient and intersection setting. Fact 2.2.6(i), p.10, gives the
stronger finite-cover Cech exactness statement whose scalar degree-zero,
unit-radius specialization motivates this target. These passages were read
directly. The implemented proof applies proved descent and comparison
lemmas rather than treating that source assertion as a formal premise.

Zero and nonreduced quotients, empty numerator tuples and rational loci,
and trivial scalar valuations remain in scope. The conclusion is scalar
degree-zero gluing at unit radii over presented strict bases. Higher Cech
exactness, admissibility, general finite-module descent, arbitrary radii,
all-affinoid test representation and analytic atlases are outside this
statement. Conversion to the categorical sheaf condition is a separate
task. The target pair and all imported pairs are unchanged.
