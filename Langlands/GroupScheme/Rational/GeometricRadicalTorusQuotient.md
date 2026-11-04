# Torus quotients by a supplied geometric unipotent radical

Worker 1333.

This internal construction produces an actual quotient over the original
field by a supplied geometric unipotent radical of a smooth connected affine
solvable group. It retains `SolvableTorusQuotientStatement` as an explicit
prerequisite. It does not prove that absolute quotient statement, existence or
splitness of the geometric radical, or the full rational conjugacy theorem.

`IsUnipotentRadical.range_eq_of_torus_quotient` compares the supplied radical
with the smooth connected normal unipotent kernel of a given torus quotient.
Radical greatestness gives containment of that kernel in the radical. The
radical is affine because its inclusion in the affine ambient group is closed.
The published vanishing theorem for homomorphisms from affine unipotent
groups to arbitrary tori makes its composite with the quotient zero.
The full represented-kernel equality gives the reverse containment on every
test scheme.

`LeviSubgroup.IsGeometricUnipotentRadical.isSplitTorus_baseChange_quotient`
applies the preceding argument over the chosen algebraic closure. The given
geometric radical predicate supplies radical maximality there, and the
published field-extension and connectedness results preserve the ambient
group's hypotheses. The absolute quotient premise supplies an actual split
torus quotient and its smooth connected normal unipotent kernel. The two
quotients therefore have the same full scheme kernel. Their projections are
quasi-compact: this is assumed for the original quotient and preserved by
base change, while the absolute projection is a morphism between affine
schemes. The published `FppfQuotientComparison.iso` identifies their actual
group-scheme targets. Transport across this isomorphism gives splitness of
the base change of the original target.

`GeometricRadicalTorusQuotient i` extends the published
`SmoothNormalQuotient i` data by splitness of its target over the algebraic
closure. It retains the actual original-field target and projection, target
smoothness, separatedness, finite type and quasi-compactness, a smooth
surjective quasi-compact projection, and its exact represented fppf kernel.
Its `isTorus` theorem uses that same algebraic closure as a splitting field
in the unchanged torus predicate.

`LeviSubgroup.IsGeometricUnipotentRadical.torusQuotient` chooses the published
smooth normal quotient of the supplied radical. The comparison theorem
attaches geometric splitness to its target, giving the defined data over
every ground field and at the original universe.

All provenance is internal: the construction composes the cited Library
quotient, comparison, base-change and vanishing interfaces. It introduces no
new assertion from the literature and retains its one absolute quotient
prerequisite.
