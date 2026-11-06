# Actual quotients of normalized-exponent tempered representations

This derived supporting unit supplies quotient closure for the normalized-exponent
temperedness predicate used in Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026, VII.2.6, first proof paragraph, printed p.231 / PDF p.237.
That proof selects an irreducible quotient of a unitary Jacquet module and uses
the tempered square-integrability criterion on the quotient. The present unit
isolates the quotient step. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`normalizedTemperedQuotient` constructs the actual smooth quotient by a
supplied invariant subrepresentation, bundled with a proof of
normalized-exponent temperedness. Its underlying object is literally
`SmoothRep.quotient π S`, whose carrier is the module quotient by `S`.
`normalizedTemperedQuotientMap` is the canonical equivariant projection to
this bundled object; its surjectivity theorem uses the actual module quotient
projection. No abstract quotient object is chosen. The construction uses the
quotient-closure proof described below.

The field and the two representation carriers have independent universes
`u`, `v`, and `w`. The ambient group is over a Hausdorff nonarchimedean local
field, with its canonical rational-point topology and the supplied locally
compact and nonarchimedean-group instances. Every specified actual parabolic,
rational Levi, geometric radical, multiplication isomorphism and split component
is retained.

`jacquetIntertwining_surjective` proves surjectivity of the published actual
normalized Jacquet map. Localization lifts a representative through the original
surjection; inverse-half-modulus normalization leaves the linear map unchanged.

`isNormalizedJacquetExponent_of_surjective_intertwining` reflects every target
normalized exponent to the source. Here admissibility of the source's actual
Jacquet module is an explicit premise. It gives a spanning family of central
weights. The published weight-reflection theorem applies to the onto Jacquet
map, since that map intertwines the identical actual split-component actions.
The target Jacquet module only needs smoothness. The same character occurs on
both sides, so its open kernel and normalized real part are unchanged.

`unitaryJacquetPart_eq_bot_of_surjective_intertwining` transfers vanishing of
the actual unitary Jacquet part to a smooth quotient. A nonzero target weight
with zero normalized real part would reflect to a nonzero source weight lying
in the zero source unitary part, a contradiction. This result retains the
source Jacquet-admissibility premise.

`IsNormalizedExponentTempered.of_surjective_intertwining` removes that premise
when the source is tempered. The published pointwise Jacquet-structure theorem
derives actual Jacquet admissibility using the source's compatible presentation
coverage. Compact-open averaging makes the target fixed-vector space a quotient
of the corresponding finite-dimensional source fixed-vector space; passing
from a contained compact open subgroup to any open subgroup proves target
admissibility. Every target exponent reflects to a source exponent, whose cone
membership follows from source temperedness. Compatible presentation coverage
is copied from that same source condition. The theorem adds no presentation,
Jacquet-admissibility, finite-length, central-character or quotient-compactness
premise. `of_surjective` is its fixed-universe categorical form.

This is an internal construction and derivation from the published smooth
module quotient, actual Jacquet maps, central weight decomposition and compact
averaging. It does not prove temperedness of a unitary Jacquet module
(VII.2.3), nested Jacquet transitivity, the minimality-to-square-integrability
step, or any final VII.2.6 proposition.
