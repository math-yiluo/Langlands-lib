# The actual Jacquet image of the cut complex

This internal construction fixes an arbitrary supplied p-adic field and
topological data, a rank, a target block shape `C`, and a complex representation
`ρ` of the general linear group. The field and coefficient universes remain
independent. No smoothness, irreducibility, finite length, or dimension
assumption is added. The construction includes rank zero and degrees with no
coordinates.

The auxiliary `EquivariantDiagram.jacquetDiagram` first applies the actual
normalized Jacquet functor to a general equivariant cut diagram.
`ActualCutComplex.jacquetDiagram` specializes this to each
actual induction--Jacquet cut term and each actual `Transition.cutMap`.
Its objects are the actual `C.JacquetModule` quotients, and its inclusion maps
are the linear maps underlying `T.normalizedJacquetMap`, as recorded by
`jacquetDiagram_map`.
On quotient representatives these maps are the quotient classes of the
original transition maps. Surjectivity of the quotient maps, together with
identity and composition for the original cut diagram, proves the two diagram
laws. No graded identification or geometric support assertion enters these
laws.

`totalQuotient` and `degreeQuotient` send a family to its coordinate Jacquet
classes. Quotient maps preserve zero, so they commute with extension by zero
and homogeneous restriction. They commute with each signed insertion because
the actual Jacquet transition sends a representative to the class of its
actual transition image and complex linearity preserves its exterior sign.
Summing proves `totalQuotient_differential`, and homogeneous extension and
restriction give `degreeQuotient_differential`. These are equalities of actual
maps applied to every family.

`jacquetDegreeEquiv` specializes the canonical finite-product Jacquet
equivalence to the cut sets of each degree. It identifies the actual Jacquet
quotient of the original degree product with the corresponding homogeneous
product of the Jacquet diagram. On representatives it is exactly
`degreeQuotient`. `jacquetDegreeRepresentation` equips that homogeneous product
with the actual coordinate normalized Levi actions, and
`jacquetDegreeEquiv_intertwining` proves equivariance for the supplied actual
block modulus.

Finally `jacquetDegreeEquiv_differential` states the commuting square for the
actual normalized Jacquet image of `ActualCutComplex.differential` and the
actual signed differential of `jacquetDiagram`. The proof reduces an arbitrary
Jacquet class to a representative using the surjective quotient map and applies
the previously proved homogeneous quotient square. Thus this comparison
retains both the actual transition maps and their existing exterior signs.

The provenance is internal: the published actual cut complex, actual normalized
Jacquet representative formulas, and the canonical finite-product quotient
equivalence suffice. This module supplies no geometric graded-piece
identification, orbit-integral comparison, lower exactness, or Aubert
effectivity theorem.
