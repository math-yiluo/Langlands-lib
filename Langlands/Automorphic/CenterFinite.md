# Simultaneous adelic center finiteness

For every number field `K : Type u` and every natural rank, this construction
uses the published genuine complex enveloping-center differential action on
archimedean smooth functions from
`Langlands.Global.ArchimedeanEnvelopingAction`.

`SmoothSliceFamily` is the space of families indexed by all finite adelic
matrices, with values in the actual archimedean smooth-function space.
`centerFamilyAction` applies one center element to every slice. Its algebra
homomorphism laws follow pointwise from the actual differential action.
The entire family has one orbit map, one orbit span and one annihilator ideal.
`IsCenterFiniteFamily` requires this orbit span to be finite-dimensional over
the complex numbers. The orbit span is the range of its complex-linear orbit
map. The first isomorphism theorem identifies that range with the complex
quotient by the common annihilator, proving the finite-codimension equivalence.
The existential formulation is also equivalent: there exists one ideal with
finite complex quotient that annihilates every slice. For the reverse direction,
such an ideal is contained in the common annihilator; the canonical surjection
of their complex quotient modules transfers finite-dimensionality.

`smoothSliceFamily` sends an actual smooth, continuous, rational-invariant
adelic function to its family of smooth infinite slices.
Its evaluation formula and injectivity follow from the actual finite/infinite
product decomposition of the adelic matrix group.
`centerFiniteSmoothFunctions` is the inverse image of the finite-vector
subspace for the family action. Thus its addition and scalar closure are
proved. Finite adelic right translation reindexes the family by `b ↦ b*d`.
This reindexing intertwines the center action and therefore preserves
simultaneous center finiteness, giving an actual finite adelic
subrepresentation of the smooth ambient space.
`CenterFiniteSmoothRationalFunctions` is this actual subspace's carrier.
`centerFiniteSmoothFiniteRightAction` restricts finite adelic right translation
to it, and `centerFiniteSmoothInclusion` is the injective intertwining inclusion
into the smooth ambient space. Its evaluation formula is
`f(x * ofFinite d)`. Injectivity concerns the inclusion, not faithfulness of
the finite adelic group representation.

The source is Borel–Jacquet, *Automorphic forms and automorphic
representations*, Corvallis (1979), §1.3(c), printed page 190 / one-based PDF
page 185, and §4.2(c), printed page 195 / PDF page 190. Registered source
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The source requires one finite-codimension ideal annihilating the adelic
function. Our common annihilator enforces that simultaneous condition;
separate finite-dimensionality of each slice would not suffice. The
family representation and inverse-image construction are derived
implementations using the published finite-vector API.

No differential operator is asserted here to preserve joint adelic continuity
or the rational-invariant ambient space. No full infinite-factor translation
stability or identification with the complete automorphic space is asserted.
Those additional constructions remain separate obligations.
