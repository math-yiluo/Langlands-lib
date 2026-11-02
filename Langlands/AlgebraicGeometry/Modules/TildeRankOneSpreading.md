# Rank-one stalk spreading for associated sheaves

This internal derived unit starts with a finitely presented module `M` over a
commutative ring `R` and a rank-one linear equivalence at an actual stalk of
the associated sheaf on `Spec R`. The scalar ring of the input equivalence is
the actual local ring of `Spec R` at that point.

`exists_tilde_localization_trivialization` proves that some element outside
the point's prime ideal gives an actual trivialization of the sheaf's ordinary
pullback to the spectrum of that element's localization. Mathlib identifies
the actual sheaf stalk as a localized module. Its finite-presentation theorem
lifts the stalk equivalence to an equivalence between the away-localizations
of `M` and the regular module `R`. The standard localization--tensor
comparisons turn this into a rank-one equivalence after scalar extension.
The published `tildePullbackAlgebraIso` then converts this into an isomorphism
of actual sheaves, followed by Mathlib's `tildeSelf` comparison with the
structure module.

`mem_rankOneLocus_tilde_of_stalkEquiv` identifies the localization spectrum
with its principal open image. Restriction agrees with pullback along this
open immersion, and the published exact restriction formula for the rank-one
locus places the original point in that locus.
`tildeRankOneTrivializingNeighbourhood` chooses an actual open neighbourhood
with the point-membership and existence of a sheaf trivialization. This
choice is noncomputable; no compatibility with the given stalk equivalence
or between choices is claimed.

The provenance is the stated composition of Mathlib localization spreading
and the published actual sheaf-pullback and rank-one-locus constructions.
No extra literature assertion or noetherian hypothesis is introduced.
The scope is an associated sheaf with a finitely presented defining module;
the reduction of an arbitrary locally finitely presented sheaf to this
situation is a separate step.
