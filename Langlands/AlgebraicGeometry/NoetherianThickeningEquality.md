# Equality near a closed subscheme from its infinitesimal neighbourhoods

For two `S`-maps `f` and `g` from `X` to `Y`, `agreementOpen f g` is
the union of affine opens of `X` on which the ideal of their relative
equalizer is zero. When `Y` is separated over `S`, the equalizer is a
closed immersion. The inclusions of those affine opens factor through
it, so the two maps agree on their union.

Suppose additionally that `X` is locally Noetherian and that the maps
agree on the closed subscheme cut out by `I^(n+1)` for every `n`. The
equalizer ideal then lies in each positive power of `I`. On each affine
chart, the uniform Krull intersection theorem supplies an element `r`
of `I` such that `1 - r` annihilates the equalizer ideal. The principal
open defined by `1 - r` contains the zero locus of `I` in the chart
and has zero equalizer ideal. Hence the zero locus of `I` is contained
in `agreementOpen f g`.

`exists_open_eq_of_eq_on_infinitesimal_neighbourhoods` gives this open
as a witness containing the zero locus of `I` on which the maps agree.

This is an internal consequence of the published uniform Krull intersection
theorem in `Lie.SubgroupEqualityAlgebra` and Mathlib's closed equalizers,
ideal-sheaf subschemes and gluing along opens.
