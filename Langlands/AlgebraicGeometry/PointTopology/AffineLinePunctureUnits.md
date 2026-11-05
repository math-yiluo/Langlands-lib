# The actual punctured-affine-line topology and units

This derived comparison implements the opening argument of section 3 in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
pp.3–4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The polynomial coordinate localization at the single variable is used as an
auxiliary presentation. A point sends the variable and its actual inverse
section to a pair of mutually inverse elements. Conversely, evaluation of the
variable at a unit extends uniquely through the localization. The two maps are
inverse by the localization universal property and polynomial generator
extensionality.

The homeomorphism uses the existing evaluation topology on algebra points and
the existing units topology, induced by the value and inverse coordinates.
Continuity toward units follows from evaluation at the variable and its inverse.
For continuity of the inverse map, every localization element has the form
of a polynomial numerator times a power of the variable's inverse. Evaluation
is therefore continuous by polynomial evaluation, multiplication and the
continuous inverse-value coordinate of the units topology.

`affineLinePunctureIsoAway` uses Mathlib's actual scheme isomorphism
`basicOpenIsoSpecAway` to identify the previously constructed open subscheme
`affineLinePuncture R` with the relative spectrum of the polynomial localization.
The compatibility with the specified base morphism follows from the algebra
scalar tower. The composite with the spectrum map of the localization algebra
map is proved to be the actual open inclusion `affineLinePunctureι R`.
Affineness of the open subscheme follows from the affine basic-open theorem.

`affineLinePunctureUnitHomeomorph` composes this relative isomorphism's existing
homeomorphism on affine scheme points, the published spectrum/algebra-point
homeomorphism, and the localization homeomorphism above. Thus both the
punctured scheme's independent global-section evaluation topology and the
usual topology on units are retained. Its unit's value is proved equal to
`affineLinePointEquiv R S (p ≫ affineLinePunctureι R)`. The commutative comparison
identifies the actual point inclusion with `Units.val` in the affine-line
coordinate.

The algebra-point comparison allows independent base and value-ring universes;
the scheme comparison uses their common arbitrary universe. Both apply to
arbitrary commutative topological value rings and arbitrary base algebras.
Neither the unit locus's openness nor the inclusion of units being an embedding
is assumed. Conrad describes the same units topology using the hyperbola
presentation; the implemented route uses the canonically isomorphic coordinate
localization. The comparison is a derived construction, and does not by itself
assert an arithmetic nonembedding result.
