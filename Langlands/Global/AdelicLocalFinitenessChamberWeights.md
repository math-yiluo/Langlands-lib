# Log weights for root chambers and central orthants

`localFinitenessLogWeight` adds a weighted sum of the normalized simple-root
coordinates to a weighted sum of the absolute central coordinates. It is
continuous. If every rate is at least `c ≥ 0`, then on any fixed lower root
chamber it dominates `c` times the product supremum norm up to the displayed
constant depending on the lower thresholds. A root unit shift adds its rate.
An outward central unit shift on either side of an orthant adds the central
rate, including on the wall.

`AdelicLocalFinitenessChamberWeightStatement` applies this construction in
real linear coordinates on an actual parabolic character dual with a finite
free lattice of rational characters and a supplied Iwasawa compact. It gives a
continuous log weight with uniformly bounded displacement under right
translation by each fixed compact set when the central rates are nonnegative.
For a positive-rank closed matrix embedding `ρ`, it also bounds the exponential
of the log weight by `C` times the adelic representation height for `ρ` raised
to the real power `t`, with `C > 0` and `t ≥ 0`. The proof represents each
linear coordinate form by a real character parameter using a finite integer
basis of the character lattice. The log weight then equals the maximum over all sign
choices for the central terms, and the estimates follow from the finite
maximum theorem for Iwasawa character weights.

This realizes the signed weights of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, §7.3 and §7.7, as a single weight on the
full root chamber. Its growth and displacement estimates are the inputs to
the weighted smoothing argument. Its coordinate shifts and lower bound are
the inputs to the slab and finite-measure estimates.
