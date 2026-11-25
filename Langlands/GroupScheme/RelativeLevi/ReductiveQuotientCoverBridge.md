# From an etale cover to pointwise dynamic presentations

This supporting component belongs to the exact proof of
`RelativeParabolicReductiveQuotientStatement`. It assumes the published
cover-form proposition `RelativeParabolicEtaleLocalDynamicStatement`; it does
not prove that proposition or the unconditional quotient target. The final
assembly in `ReductiveQuotientProof` discharges its premise with the published
theorem `relativeParabolicEtaleLocalDynamic`.

`RelativeLevi.pointwise_dynamic_of_etaleLocalDynamic` takes that proposition,
a reductive group scheme over any scheme, and a supplied relative parabolic
inclusion. Its conclusion is exactly the pointwise etale-neighbourhood premise
of the conditional quotient-existence and radical-annihilation helpers. For
each base point, `Scheme.presieve₀_mem_precoverage_iff` applied to the cover's
`mem₀` supplies a cover member and an actual point above it.
`Scheme.Cover.map_prop` supplies etaleness of that member, and
the cover's dynamic presentation supplies the cocharacter and representation
of the actual pulled-back inclusion. No restriction on the base or its points
is introduced; an empty base is also allowed. The universe is arbitrary.

The provenance is internal conversion of the published statement's covering
family into pointwise witnesses using Mathlib's cover API. No new assertion
from the literature is made.
