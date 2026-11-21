# Local pole transfer from automorphic tests

`HasHolomorphicNumerator` is a local presentation of a family in a fixed
uniform-growth stage. It supplies a scalar holomorphic denominator that is nonzero
somewhere and a weakly holomorphic numerator. Their defining relation holds on the
intersection of the presentation and agreement domains.

`exists_uniform_holomorphic_evaluations_of_automorphic_tests` assumes a connected
open presentation domain and weak holomorphy on the open agreement set. The numerator
is automorphic on their intersection. A family of continuous scalar tests separates
automorphic vectors, and its values on the original family extend holomorphically on
the presentation domain. The theorem gives one smaller open neighborhood and a
holomorphic extension for each continuous scalar evaluation.

The proof chooses a direction and a circle using the denominator alone. For every
base point in the agreement set, the corresponding disk meets that set in a nonempty
open subset. On the disk, the scalar identities between the tests of the numerator
and the extended tests multiplied by the denominator follow by the identity theorem.
The Taylor coefficient argument in `AdelicTaylorPoleDetection` then gives analytic
division for each scalar evaluation at every point of the disk. The translated circle
average in `HolomorphicSliceDivision` produces its holomorphic extension. Equality
with the original evaluation holds off the zeros of the denominator and extends to
the whole agreement set by continuity. Local nonvanishing somewhere follows from
the scalar identity theorem on the presentation domain.

`exists_uniform_holomorphic_evaluations_of_cuspidal_pairings` uses the actual norm-one
Levi pairings of standard constant terms and the order-zero point evaluations.
Weighted majorants give continuous pairing forms and absolute convergence.
`LeadingCuspidalInjectivityStatement` gives separation through the explicit zero
projections in `AdelicCuspidalPairingDetection`. The hypotheses include holomorphic
extensions of the pairings on the same presentation domain. The conclusion gives one
neighborhood for the extensions at all adelic points.

The construction is a derived route to the pole-detection argument of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §8.6,
pp. 225–226. The pairing and separation use §6.2, (6.8), and §6.3, Theorem 6.3.
For an application to root poles, the input family is the meromorphic family
multiplied by the proposed root product. The existence of the meromorphic
presentation, weighted test bounds, leading injectivity and the identities giving
holomorphic extensions after that multiplication remain the inputs to this construction.
