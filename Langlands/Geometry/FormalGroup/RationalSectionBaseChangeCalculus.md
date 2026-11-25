# Coefficient pullback of section composition, inverses and local isogenies

This module derives structural laws and actual isogeny constructions
from the coefficient pullback of the genuine rational Hom sheaf. It claims
no separately sourced theorem.

Let `O` be a commutative ring, `R` and `S` commutative `O`-algebras and `F`
an `O`-algebra field. The rings `R`, `S` and `F` occupy one universe; `O`
can occupy a different one. Coordinate types are finite and may differ.
Every construction uses an actual coefficient map `φ : R →ₐ[O] S` and
the actual inverse-image open under `Spec S → Spec R`.

`RationalSection.baseChange_id` proves preservation of the actual identity
section by its global tensor formula.
`RationalSection.baseChange_comp` proves preservation of composition on all
actual rational sheaf sections. The proof takes the covering image sieve of
the product of the two genuine sheafification units. On that covering sieve,
both sections have tensor representatives, and the existing coefficient-square
map preserves their tensor composition. Restriction compatibility identifies
these local equations with restrictions of the desired equation. Separatedness
of the actual pushforward target sheaf then gives the equation on the whole
open. No global representatives or uniform denominators are assumed.

`baseChange_ofIntegral` identifies the pullback of an actual integral numerator
with the image of `Hom.openBaseChange`. `Hom.IsIsogeny.openBaseChange` proves
that this numerator is an actual isogeny: ordinary coefficient extension
preserves its actual finite projective kernel and affine fppf lifting condition,
and the canonical coefficient-square isomorphisms transport these conditions
to the target formal modules.

`IsLocallyScalarIsogeny.baseChange` pulls a witnessing neighbourhood back to
its actual inverse image, keeps its original natural-number scalar exponent,
and uses this actual extended numerator. Linearity and the restriction and
integral-image formulas give its required scalar equation.
`LocalQuasiIsogeny.baseChange` therefore constructs an actual local
quasi-isogeny on the inverse-image open, retaining scalar nonvanishing and
using the published coefficient stability of the two scalar-divisibility
conditions. It commutes with restriction.

`RationalSectionIso.baseChange` pulls back both actual inverse sections.
Preservation of section composition and identities proves the two inverse
equations. This construction commutes with restriction, preserves identities,
inverses and composition, and agrees with the existing coefficient maps on
integral isomorphisms and global tensor quasi-isogenies. Only the last
comparison additionally assumes that `O` is a domain and `F` its fraction field.

This module does not construct an inverse for an arbitrary local quasi-isogeny,
prove finite-kernel composition, or identify local quasi-isogenies with
all invertible rational sections. The identity and composition laws for
successive changes of the coefficient ring are proved in
`RationalSectionCoefficientCoherence` (`RationalSection.baseChange_identity_transport`
and `RationalSection.baseChange_composite_transport`).
