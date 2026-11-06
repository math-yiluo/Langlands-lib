# Actual parameters for length-one Tadic factors

Author: Worker 1431. Derived local construction.

This pair constructs actual unitary parameter realizations for a supplied
length-one Speh representation and its supplied complementary product. It
uses the exact `spehLengthOneComparison` proof, the elementary singleton and
repeated-pair parameters, and the general `UnitaryParameterRealization`
structure. It assumes the supplied Speh relation and length equality. It
does not derive either hypothesis from genericity or unitary classification.

Fix an arbitrary prime `p`, `F : PadicField.{uF} p`, and compatible topology
`T`. The field and representation universes remain independent; actual
smooth carriers lie in `Type (max uF uV)`. Induction is the existing
normalized standard upper-block induction.

Let `d : SpehDatum F T`, let `S` be an actual smooth representation of
`GL_(d.degree)(F)`, and assume `hS : d.IsSpeh S` and
`h1 : d.length = 1`. The source degree is
`d.degree = d.length * d.rank`. The equality `h1` gives an explicit equality
`d.degree = d.rank`. The exact length-one comparison identifies the rank
transport of `S` with the actual source block `d.delta`.

`blockProperties_lengthOneSpeh` transfers the three source block properties
along this isomorphism: irreducibility, existence of an invariant positive
Hermitian form, and analytic square-integrability. Its private transport
lemma eliminates the rank equality and applies the established invariance
theorems for actual representation equivalences. The source properties come
from `hS.1`; no analytic square-integrability condition is inferred from a
numerical exponent or an abstract representation label.

The output states these properties for `S` at its original rank
`d.degree`. The subsequent constructors therefore reuse exactly this
supplied actual representation as their unitary square-integrable block.
No transport through a determinant twist is needed.

`lengthOneSpehParameterRealization` uses the positive one-block shape of
total rank `d.degree`, the constant block `S`, and exponent zero.
`isUnitaryGenericDatum_singleton` supplies the exact parameter conditions
from the transferred block properties. The inverse of
`singletonUnitaryProductIso` compares `S` with its entire one-block
twisted product.

For every real `α` with `0 < α` and `α < 1/2`,
`lengthOneComplementaryParameterRealization` uses the two-block uniform
shape of total rank `2 * d.degree`, the same actual `S` at both indices,
and exponents `α` and `-α`. The elementary paired validity theorem proves
both strict bounds and the occurrence-preserving Hermitian matching. The
resulting actual twisted product is definitionally `d.complementaryInduced
S α`, so its comparison is the identity isomorphism. The endpoints of the
complementary interval remain excluded.

Both constructors produce actual data and maps in
`UnitaryParameterRealization`. That structure's existing rank transport and
isomorphism pullback operations can pass these data to another actual
representation of the appropriate rank, and its finite product operation
can assemble supplied local realizations.

The provenance is entirely derived from these established comparisons and
finite parameter constructions. This pair supplies no new assertion from
Tadic's classification theorem. It neither proves nor assumes
`TadicUnitaryDualExhaustion`, higher-Speh genericity elimination, or
`UnitaryGenericExhaustion`. Those remain distinct mathematical obligations.
