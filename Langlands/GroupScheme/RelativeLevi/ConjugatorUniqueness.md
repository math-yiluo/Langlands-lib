# Uniqueness of unipotent conjugators from self-normalization

Worker 639.

This is an internal construction and algebraic reduction for
`RelativeLeviConjugacyStatement`. It does not prove that statement. All bases
are arbitrary schemes in universe `u`.

`RelativeLevi.radicalConjugate l r u` is the image of `l` after conjugation
by the image of the actual global point `u` under `r`. Its value is the
subgroup functor on all test schemes used by the published conjugacy target.

The implemented argument has three steps:

1. If two points `g` and `h` give equal conjugate images of a monic subgroup
   `l`, the point `h⁻¹ g` normalizes its image on all test schemes. Postcompose
   the image equality with `Int(h)⁻¹`, use `innerIso_mul_hom`, and compare the
   two monic representatives of the resulting equal image. Their source
   isomorphism witnesses normalization through the published
   `SubgroupFunctor.mem_normalizer_range_of_innerIso`.
2. An actual isomorphism `subgroupMultiplication l s` makes the two subgroup
   images meet only at the identity on every test scheme. Apply the first
   coordinate `leviComponent l s` to an equality `l(a) = s(n)` to obtain
   `a = 1`, and then the original point is the identity.
3. If the all-test normalizer of the image of `l` is contained in that image,
   and the acting monic subgroup `r` is contained in `s`, the quotient of any
   two conjugators lies in both factors and hence is the identity. Cancel
   the monomorphism `r` to get equality of the original `U(S)` points.

`radicalConjugate_injective_of_range_le` is the general version of step 3.
It requires monomorphisms of `l` and `r`, an actual multiplication isomorphism
for `l` and `s`, containment `range r ≤ range s`, and the supplied all-test
normalizer inclusion. It uses no reductivity, smoothness, normality, fibre
hypothesis, or assumption that the two factors are distinct.
`radicalConjugate_injective` specializes to `s = r` and normalizer equality.

`relative_radicalConjugate_injective` obtains those algebraic hypotheses from
a relative Levi and specified relative unipotent radical, assuming the
**entire propositions** `RelativeUnipotentRadicalStatement` and
`RelativeLeviSelfNormalizerStatement` as explicit inputs. Radical uniqueness
identifies the specified radical image with the radical image in the Levi
multiplication witness. Closedness supplies both monomorphisms. The result
proves injectivity, including for target subgroups which are not Levi.

Finally, `existsUnique_conjugator_iff_exists` rewrites uniqueness plus existence
as existence alone under the same two geometric inputs. The target `l'` is
arbitrary; the theorem does not need a Levi hypothesis on it. Existence of a
conjugator, existence of relative radicals, and Levi self-normalization have
not been established by this module.

The provenance is internal and derived: this is elementary algebra applied to
the published `SubgroupFunctor.range`, `innerIso`, `IsRepresentedBy` and
`leviComponent` constructions. It introduces no additional geometric axiom
or literature assertion. In particular it neither imports nor assumes an
unpublished proof of either relative geometric statement. The original
statement modules and their dependencies are unchanged.
