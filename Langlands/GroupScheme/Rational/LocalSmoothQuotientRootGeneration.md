# Integral root generation in smooth fibre-quotient kernels

This module concerns a smooth affine group scheme with geometrically
connected fibres over a local domain, a map from a coordinate split torus, and a
smooth homomorphism from a field fibre to a smooth affine field group. The source
torus map on a possibly different field fibre is monic and has a relative root
system. The two field fibres need not be field extensions of one another.

`baseChangeQuotientKernel` is the subgroup of original integral sections whose
restriction followed by the specified field-fibre homomorphism is the identity.
It records the original sections rather than their generic images.

`baseChangeSectionHom_orderedPoints` proves that restricting an ordered product
restricts each original coordinate, using the section homomorphism's preservation
of list products and its naturality. The general ordered-chart bound then
transfers coordinatewise kernel reflection and bounds on root intersections to
a bound on the entire chart's kernel intersection.

`dynamicUnipotent_inf_baseChangeQuotientKernel_le_of_exponentRoots` proves that a
subgroup containing all original integral root intersections with this kernel
also contains the entire dynamic-unipotent intersection. Roots are selected by
the given relative root system on the first field fibre. They are enumerated
and written as integer exponent characters. Their original smooth integral root
representatives give the integral ordered product chart. The integer exponents,
the enumeration and disjointness of positive root rays transport to the quotient
field fibre. The smooth quotient root-product theorem there reflects membership
in the full homomorphism kernel in every restricted original root coordinate.
Multiplying these original integral coordinates proves the claimed containment.

The proof is an internal composition of the existing integral ordered-root chart,
field character transport and smooth quotient coordinate-reflection results.
It assumes neither surjectivity of the field-fibre map nor connectedness or
unipotence of its kernel. It does not give generation of the whole section
kernel, which additionally requires a centralizer and opposite-cell argument.
