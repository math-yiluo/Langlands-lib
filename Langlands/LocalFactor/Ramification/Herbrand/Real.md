# Real polygon used for the Herbrand construction

Worker 60 implements the elementary real analysis underlying the actual
Herbrand function. This module is an internal helper, not a replacement
ramification filtration or a local-field input record.

For natural numbers `g i` and a cutoff `b`, the function `polygon` is the
identity below zero. For nonnegative `u` it is

`(u + sum (i < b) (g(i+1)-1) min(1,max(0,u-i))) / g(0)`.

When `g i` are the orders of lower ramification groups and these orders are
one after `b`, this is Serre's polygon. The constant term `u` retains the
strictly positive slope `1/g(0)` after termination. Positivity of the orders
implies that all ramp coefficients are nonnegative. Each ramp is continuous
and nondecreasing. These facts prove continuity and strict monotonicity of
the polygon. A lower bound by `u/g(0)` on the positive half-line and the
identity on the negative half-line, together with the intermediate value
theorem, prove surjectivity. `polygonOrderIso` and `inverse` are constructed
from these proofs; an inverse or bijectivity certificate is not an input.

The whole-real extension below -1 is an implementation convention. The
ramification construction restricts to Serre's half-line `[-1,infinity)`.
No arithmetic subgroup, quotient, tower, or reciprocity theorem is used.

Original source: Jean-Pierre Serre, *Local Fields*, Greenberg translation,
GTM 67 (1979), Chapter IV, section 3, Proposition 12 and the definition of
its inverse preceding Proposition 13, printed page 73 (retained PDF page
80). Source `serre-1979-local-fields`, retained file
`C:/Central-Library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The finite ramp representation is an internal implementation of that
piecewise linear function. `polygon_on_unit_interval` proves its affine
formula on each closed unit interval: ramps before that interval are one,
the current ramp is its fractional coordinate, and later ramps are zero.
The eventual-one hypothesis permits replacing the cutoff sum by this
interval's finite prefix, even beyond the cutoff. `polygon_floor` then
uses the natural floor bounds to give the source formula exactly.

This module uses only pinned Mathlib results: continuity of finite sums
and min/max, the intermediate value theorem
`mem_range_of_exists_le_of_exists_ge`, and
`StrictMono.orderIsoOfSurjective`. Native and Lake development compilation
succeeded without diagnostics. Independent review and publication remain
separate from these checks.
