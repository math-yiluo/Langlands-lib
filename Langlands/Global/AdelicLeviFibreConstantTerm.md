# Levi fibres of continuous parabolic functions

`leviFibre` restricts a right translate of the ambient function to the actual Levi points. It preserves continuity and descends under the rational Levi when the input is invariant on the parabolic quotient. The height of a point in the restricted representation is its height after inclusion into the ambient group. A fixed right translation changes a polynomial bound only by a constant factor, by submultiplicativity.

For nested standard parabolics the Levi retraction of the larger one restricts to a projection from the smaller parabolic's radical onto the represented intersection with the larger Levi. The kernel coordinate lies in the larger parabolic's radical on every test scheme, and an element of the intersection already lifts to the smaller parabolic's radical. This is the Levi decomposition used in the passage to smaller Levi quotients in Mœglin–Waldspurger I.3.4.

`subgroupConstantTerm_leviFibre` assumes the displayed all-test intersection is represented by a closed subgroup of the Levi with compact rational quotient. The projection preserves the normalized quotient probability by `measurePreserving_radicalQuotientProjection`. The Levi integrand descends because the fibre is rational-Levi invariant. Pulling it back to the ambient radical quotient gives the ambient integrand: its larger radical coordinate acts trivially on the input function. Both averages are therefore equal at every ambient translate and every Levi argument.

- `moeglin-waldspurger-1995-cuspidal-components`, `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, 05.3_pp_40_48_Cuspidal_components.pdf, I.3.4, p. 45, passage to smaller Levi quotients.
