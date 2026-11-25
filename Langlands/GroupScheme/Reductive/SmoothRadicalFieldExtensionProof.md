# Represented radicals under algebraically closed field extension

`Langlands.GroupScheme.smoothAlgebraicallyClosedUnipotentRadicalExtension.{u}`
proves the published
`SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement.{u}` at its
arbitrary universe parameter. For algebraically closed fields `k K : Type u`
with `Algebra k K`, it preserves every supplied represented unipotent radical
`r : U ⟶ P` under the actual `GroupScheme.baseChange` along `Spec K ⟶ Spec k`
when the ambient group `P` is smooth. The existing `IsUnipotent` fixed-vector
predicate and `IsUnipotentRadical` predicate, including normality and greatestness
on every test scheme, are unchanged. The ambient group may be nonaffine and
disconnected, and the extension may be transcendental.

The implemented proof applies the published theorem
`smoothAlgebraicallyClosedUnipotentRadicalExtension_of_antiAffineQuotientExistence`
to the published proof `antiAffineQuotientExistence`. The latter proves
`AntiAffineQuotientExistenceStatement.{u}` over every field, so it supplies the
actual anti-affine quotient required for the smooth connected identity component
in the former theorem.

The conditional theorem constructs a component radical as the full inverse
image of the radical of the smooth connected affine quotient. Its anti-affine
kernel is smooth, connected and unipotent for the existing fixed-vector
predicate, both before and after the extension. Smooth quotient preservation
therefore preserves that component radical. The actual identity-component
base-change comparison and the source comparison for represented radicals
transport this conclusion to the supplied ambient radical. These constructions
retain the full radical predicate and the actual subgroup maps.

This module is derived internal content: it composes the two imported published
theorems, with no additional geometric or field hypotheses and no new external
source assertion. The imported quotient-existence proof and conditional
reduction have their own paired explanations of their constructions and
provenance. This application discharges the quotient-existence premise of the
conditional reduction and proves the unrestricted published proposition
`SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement.{u}`.
