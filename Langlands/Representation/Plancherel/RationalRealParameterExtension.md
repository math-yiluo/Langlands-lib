# Real parameters realized by actual valuation-image characters

This internal construction extends positive characters of an actual split torus
along an actual group-scheme morphism whose map on actual integer valuation
images is injective. It then specializes to the actual split component of a
connected reductive group, using the published injectivity theorem. The field
is any nonarchimedean local field in the existing interface, in arbitrary
universe and characteristic. All groups, character lattices, valuations and
image groups are the existing actual objects.

`SplitTorus.pointRealFunctional hA phi` pairs the supplied real character
parameter with the positive valuation of each actual point. Its multiplicative
codomain is the additive real numbers. The published description of the
valuation kernel proves that this functional vanishes on the actual common
norm kernel. `SplitTorus.positiveImageFunctional` therefore descends it through
the quotient by that kernel and the existing quotient-to-image equivalence.
Its projection law recovers the original point pairing. Exponentiating this
functional by the existing `rationalImagePositiveCharacter` and pulling it back
to actual points gives exactly `SplitTorus.positiveCharacter hA phi`.

`exists_rationalImageRealFunctional_extension` uses Mathlib's injectivity of
divisible additive groups (`Module.Baer.of_divisible` and its additive
homomorphism extension property) for the real numbers. It extends any real
functional on the source actual image along an injective
`rationalValuationImageMap j`. No continuity requirement is imposed on the real
functional. The exponentiated image character is continuous because its actual
image group is discrete.

Applying that extension to `positiveImageFunctional` and exponentiating proves
`exists_positiveImageCharacter_extension_of_injective`. This is an equality of
actual point characters: restriction of the positive character from the target
image is precisely the positive split-torus character of the supplied parameter.
The proof evaluates the extension equation at the actual valuation of a point,
uses the published image-map projection law, and compares the exponential
formulas. In particular, the witness is positive at every image point.

For `exists_positiveImageCharacter_extension`, the actual morphism
`j : A.toGrp ⟶ M` satisfies the published predicate `IsSplitComponent j`, and
`M` satisfies `IsConnectedReductive M`. The existing
`rationalValuationImageMap_injective` discharges injectivity from the proved
finite-index algebraic-character restriction theorem. Splitness of `A` is
explicit. The resulting `normalizedRealPart_imageCharacterPullback_surjective`
uses the published normalized-real-part law of the positive character to
realize every real parameter. This is the residue-cardinality-normalized
parameter with negative exponent, preserving central directions and rank zero.

The provenance is internal: actual valuation-kernel and quotient laws,
injectivity of the actual image map, divisibility of the reals and the existing
positive-character construction prove the results. No smooth real descent
theorem, equality of split-central ranks, finite index of the image map,
real-part surjectivity or character-extension result is assumed. The result
does not prove uniqueness of an extension, identify all smooth real
homomorphisms on the group, or provide an intertwining convergence, rationality
or Plancherel theorem. Topological assertions about the pullback on actual
points use the separately published canonical unramified-character comparison;
they are not additional conclusions here.
