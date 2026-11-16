# Local essentially etale extensions of a DVR

Worker 252. Internal derived support for the existence of strictly Henselian
DVR extensions.

Let `R` be a domain DVR, and let `S` be a local, flat, essentially finite type,
formally unramified `R`-algebra whose algebra map is local. The module proves
that `S` is a domain and a DVR and that every chosen uniformizer of `R` remains
irreducible in `S`. No Henselianity, completeness, finite residue field, or
characteristic assumption is made.

Formal unramifiedness identifies the maximal ideal of `S` with the extension
of the maximal ideal of `R`. It is therefore principal. Essential finite type
gives Noetherianity. Krull intersection, through the published
`DVRAlgebraicBaseChange.localization_eq_zero_or_of_isNoetherianRing`, writes
every nonzero element of `S` as a power of the uniformizer times a unit.
The flat local map is faithfully flat, hence injective, so the powers of the
uniformizer are nonzero. The published elementwise criteria then prove
domain and DVR properties. The maximal-ideal equality identifies the image
of the uniformizer as irreducible.

This is an internal proof from Mathlib's local unramified-algebra theorem
(`Algebra.FormallyUnramified.map_maximalIdeal`, Stacks Tag 00UW) and the
published power-unit criteria. It is the local finite-stage mechanism
behind the DVR preservation used in Stacks Tag 0AP3; it does not claim a
strict Henselization universal property.
