# Actual supercuspidality and fixed-universe classes

Author: Worker 23. Independently reviewed construction contribution.

For an actual complex representation of `GeneralLinear n F`,
`GeneralLinear.IsSupercuspidal` requires admissibility and vanishing of the
actual Jacquet coinvariant quotient for every proper ordered block parabolic
and every conjugate of its unipotent radical. Properness is the actual condition
`B.parabolic F ≠ ⊤`, not a placeholder predicate. Conjugation is the image of the
actual matrix subgroup under `MulAut.conj g`. The quotient is exactly the module
by the span of `rho(u)v-v`, through the published Jacquet construction.
Vanishing means that this module is a subsingleton.

The predicate deliberately includes every conjugate rather than assuming a
reduction theorem from arbitrary parabolics to standard ones. These are the
ordinary GL parabolics described by ordered positive blocks and change of basis.
It does not assume equivalence with the absence of parabolic-induced
subquotients, or with compact support of all matrix coefficients. Such
characterizations require separate theorems.

The generic field/topology parameters only enlarge the domain on which this
actual algebraic vanishing and admissibility condition can be written. No
classification result over that larger domain is asserted. The canonical
specialization uses the accepted `PadicField.canonicalTopologicalData` and
requires positive rank. There is no topology, dimension or completeness
assumption on representation carriers.

`Jacquet.coinvariantsEquiv` constructs the linear equivalence induced by an
ambient intertwining equivalence. Its inverse laws are checked on actual
quotient representatives. This proves vanishing invariant under equivalence,
including between different carrier universes. Together with the published
admissibility-equivalence theorem it proves
`GeneralLinear.isSupercuspidal_iff_of_equiv`.

`GeneralLinear.SupercuspidalRep` is the full subcategory of the existing
smooth category consisting of irreducible supercuspidal objects.
`GeneralLinear.SupercuspidalClass` is its actual quotient by categorical
isomorphism at the stated carrier universe. It is not resized. Its objects
have a constructed forgetful map to the actual irreducible admissible
subcategory. The representation-to-class map and its equality criterion use
the genuine isomorphism relation. The induced map `toSmoothDualClass` is proved
injective by lifting an isomorphism back through the full subcategories.
`SupercuspidalClass.IsUnitarizable` descends the published invariant-positive-form
predicate using its proved equivalence invariance. `UnitarySupercuspidalClass`
is the resulting subtype of actual supercuspidal classes; it is not a new
axiomatic family. `PadicField.SupercuspidalClass` specializes
this class space to any algebraic p-adic field with its canonical topology.
The explicit universe order is `SupercuspidalRep.{uF,uV}` for objects,
and `SupercuspidalClass.{uV,uF}` and
`UnitarySupercuspidalClass.{uV,uF}` for classes. The p-adic-field abbreviation
also has order `PadicField.SupercuspidalClass.{uV,uF}`.
These class types live in `Type (max uF (uV + 1))`.

Source: Casselman, *Introduction to the theory of admissible representations
of p-adic reductive groups* (1995), section 5.1, printed/PDF page 46:
an admissible representation is absolutely cuspidal (supercuspidal) when its
coinvariants vanish for every proper parabolic. The same paragraph discusses
conjugacy. Pages 44--47 of the original were read. Source ID
`casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The class space further restricts to irreducibles, using the isomorphism-class
convention of Bernstein--Zelevinsky (1977), section 1.2, printed page 443
(PDF page 4), which was read directly. No classification result is assumed.
The ordered upper block geometry is documented in the imported `Blocks` pair.
Bernstein--Zelevinsky (1977), sections 2.1--2.4, printed page 446 / PDF page 7,
was also read: it supplies the standard ordered-block triples and the
admissible cuspidal vanishing convention. Source ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The quotient-equivalence construction and the category packaging are internal
derivations. Mathlib's `Representation.Coinvariants.map` and the published
`Jacquet.restrictMap` are reused rather than duplicating the quotient.
The imported category, block geometry, p-adic topology, Jacquet coinvariants,
admissibility-equivalence proof and invariant-positive-form construction are
published in Library commit `459d17160ca3aef5c5b4e8ba056125e56d9479a0`.
All twelve imported project Lean/Markdown pairs match that Library exactly.
The new file and its explicit-universe interface checks compile in Lean 4.34.0,
using Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation is separate from independent source correspondence review.
It does not yet construct preservation under character twists or the smooth
contragredient; those remain explicit intrinsic/structural obligations.
