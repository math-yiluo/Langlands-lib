# Isobaric automorphy for a single cuspidal block

`cuspidalIsobaricSingleBlock` proves the all-places isobaric conclusion when there is one inducing block. The rank sum identifies that block with the ambient rank. The single automorphic subquotient used at every place is the zero-denominator quotient of the given cuspidal realization.

At each finite place, multisegment exhaustion presents the given local component as a Langlands head. The sum of a singleton family of multisegments is its sole entry, so that component also satisfies the local isobaric predicate. Its canonical inclusion into the quotient gives the required finite intertwiner.

At each real or complex place the local construction supplies an original standard parameter, an ordered list and its irreducible quotient. The original standard module belongs to the sole block and is irreducible. The stable subspace giving the nonzero subquotient is therefore the whole original standard module. The subquotient map has zero kernel by irreducibility, so its inverse intertwines the compact and Lie operators. Composing the inverse with the parameter embedding and the zero-denominator projection embeds the ordered quotient. Composing once more with the ordered standard module's quotient projection supplies the map in the place predicate.

The source for the singleton isobaric conclusion is Getz–Hahn (2024), Theorem 10.7.5 and (10.35), printed p. 288 (PDF p. 300), `getz-hahn-2024-automorphic-representations`, SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The proof specializes the placewise constituent description to a single block and uses the given realization directly.
