# Global étale sections detected by field-valued point germs

Worker 515. This is an internal construction and proof derived from the
published analytic étale site, its point axioms, and the filtered-colimit
description of site-point fibers. No new literature theorem is assumed.

`etaleSelfPoint` supplies the canonical lift of a field-valued point to the
identity étale object. `etaleGlobalGermMap` sends a global module section to
its family of germs at these lifts.

When `pointProjection L X` is surjective, a section with all these germs zero
is zero. Equality in the filtered colimit gives, for each field-valued point,
an étale neighborhood where the restriction vanishes. These neighborhoods
jointly cover the underlying points of `X`. The sieve of arrows on which the
section vanishes is therefore covering, and the sheaf's separatedness makes
the original section zero. Applying this argument to a difference proves
`etaleGlobalGermMap_injective`. The theorem
`support_etaleSelf_eq_empty_iff` then identifies global sections of empty
`PointSupport.support` with the zero section.

This is a statement about sections over the identity object of `EtaleSite X`.
It does not assert that this point family is conservative on the whole
étale sheaf category, or that every point of every étale object lifts to `L`.
