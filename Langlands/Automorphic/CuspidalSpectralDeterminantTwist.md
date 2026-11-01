# Actual determinant twists of supplied cuspidal spectral presentations

This internal construction combines the actual finite slice, genuine tensor
presentation and supplied unramified data of an existing
`CuspidalSpectralPresentation S`. The field `F : Type uF` is a number field,
the coefficient field is complex, the rank is positive (`r + 1`), and
compactness of the additive adele quotient remains an explicit hypothesis.
The original local-factor carrier universe `uV` is independent of `uF`.
The character is an actual finite-order Hecke character.

`determinantTwistLocalFactor` uses the existing `SmoothRep.twist` with the
actual local determinant character. Finite order proves its kernel open, so
smoothness follows from the proved smooth-twist theorem. Its carrier is
the original carrier in `Type uV`, and its representation is precisely the
existing positive scalar twist.

`determinantTwist` is a complete supplied spectral presentation of the actual
full cuspidal determinant image. Its finite slice is the actual multiplied
slice with containment and nonzeroness proved. Its genuine tensor presentation
is the existing tensor determinant twist, with unchanged reference vectors
and tensor exceptions enlarged by the proved full integral character tail.
Its spectral exceptions are the old spectral exceptions union that same tail.
The actual unramified-data twist proves local irreducibility, admissibility
and the normalized Hecke equations on the entire fixed space of the new
actual component. No occurrence, factorization or spectral-existence premise
is introduced in constructing these fields from the supplied old data.

The new numerical spectral system is definitionally the pointwise unit-scaled
old system restricted to the enlarged spectral exceptional set. The scalar at
each place is the actual local Hecke-character value on the existing canonical
uniformizer. The power-trace formula multiplies by its corresponding natural
power; the Euler denominator substitutes its complex value times `X`.
The pointwise scaled old system and the new actual system agree in both
existing almost-everywhere comparison relations. The single finite trace
exception set remains uniform in every positive power.

`determinantTwistLocalComponentEquiv` compares the new presentation's actual
local component with the actual determinant image of the old local component.
It composes the new component's inverse factor equivalence, the character
twist of the old factor equivalence, and the actual old-component multiplier
equivalence. These are genuine comparisons with the same twisted local factor; it
does not identify their embeddings or their chosen complementary tensor
vectors. Their existing smooth representation classes are therefore equal.

Comparison with any commonly scaled supplied numerical system preserves and
reflects both existing almost-everywhere relations, even when the numerical
system has a different rank. The corresponding comparison equivalences for
two actual full presentation twists allow different positive ranks and
different finite exceptional sets, with independently quantified carrier
universes for the two factor families. These follow by transitivity with the
proved restricted-scaled system comparisons and cancellation of the common
pointwise unit scaling. The trace comparison still has one finite exception
set uniform in every positive power.

The fixed-rank and mixed-positive-rank
`HasSpectralSystem.determinantTwist` theorems transport an existing existential
attachment to the existing actual full cuspidal class twist. The proof
extracts the old representative and complete presentation, applies the
constructed presentation, and uses the defining class and spectral-system
identities. Ranks and both carrier universes are retained.

Provenance is internal composition of the actual determinant-image,
finite-slice, tensor, unramified-data and quotient constructions. There is no
new identification with original literature. The old actual presentation and
its supplied spectra remain necessary inputs. Existence for arbitrary
cuspidal classes, uniqueness across different slices or factors, Satake
classification, and arithmetic weak association remain separate obligations.
