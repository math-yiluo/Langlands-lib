# Actual Tate quotients by analytic relations

Author: Worker 36.

`PresentedStrictAffinoidAlgebra.ofRelations K n relations` constructs a
presented algebra from a set of actual restricted power series in n
variables. Its ideal is the topological closure of the ideal generated
by those relations. The published presented-affinoid construction gives
its actual quotient carrier, quotient norm and normed K-algebra structure.
Closedness follows from taking closure, without assuming that every ideal
of a Tate algebra is closed.

`coordinate K A i` is the image of the i-th Tate variable under A's
canonical quotient map. `relation_mem` puts each supplied relation in
the closed ideal by the inclusions into its span and then its closure.
The algebraic quotient's zero criterion gives
`presentationMap_relation`: every supplied relation maps to zero.
These intrinsic laws use neither an evaluation map out of the quotient
nor a hypothesized universal property.

The definition permits any ultrametric normed coefficient field, any
natural variable count including zero, and any set of relations.
Over complete coefficients it is an actual strict affinoid quotient;
the published carrier construction retains completeness in that case.
For incomplete coefficients it remains a normed quotient construction,
and no Banach completeness assertion is made. The unit ideal and resulting
zero algebra are allowed.

The source conventions are the quotient-norm paragraph and Definitions
2.1.1 and 2.1.2 of Berkovich's *Non-archimedean analytic spaces* (Trieste
2009), p.7. This relation-set presentation is derived infrastructure:
instead of assuming that all ideals are closed, it constructs the
closure of the generated ideal. Its extension to incomplete coefficients
uses only the published normed-ring quotient construction. The separate
statement concerns bounded maps representing solutions of the relations;
this definition does not assert an analytic domain or a structure sheaf.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
