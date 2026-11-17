# Restriction to coordinate subspaces with a fixed tail

This internal helper proves that composing a Schwartz–Bruhat function on an
adelic row of length `n` with `gaugeExtendRootRow` gives a Schwartz–Bruhat
function on a row of length `m`, provided `m ≤ n`. The map retains the first
`m` coordinates and sets every remaining coordinate to one.

For the archimedean part, the extension is a continuous real linear zero
extension plus a constant. It therefore has temperate growth. The norm of
the original vector is at most the norm of its extension, since each original
coordinate is retained. Mathlib's `SchwartzMap.compCLM` then constructs the
restricted Schwartz function. For the finite part, composition preserves
local constancy by continuity and compact support by the closed embedding
proved in `AdelicSimpleRootGaugePaddedIntegrand`.

The archimedean and finite coordinate maps commute with this extension. Thus
a pure Schwartz–Bruhat function restricts to a pure Schwartz–Bruhat function;
induction on the defining complex span proves the result for the full space.
The provenance is this internal consequence of the Library's definition of
`schwartzBruhat` and Mathlib's composition theorem. No Mellin convergence or
quotient integration formula is assumed or proved here.
