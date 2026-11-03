# All-test self-normalization from rational points and an open cell

This internal derived result works over an algebraically closed field in any
universe. The ambient group scheme is affine and locally of finite type, the
right subgroup inclusion is closed, and the left subgroup is arbitrary.
Assume that multiplication from the left and right factors is an open immersion,
that every rational normalizer point belongs to the right subgroup, and that
the left subgroup meets the normalizer trivially on every test scheme.
Then the normalizer of the right subgroup functor equals that subgroup functor
on every test scheme.

`range_subset_cell_of_rational_mem` uses the published closed representability
of the normalizer of a closed subgroup of an affine group over a field. Its
representative is locally of finite type, hence Jacobson. If any point of the
representative mapped outside the open multiplication cell, the closed
preimage of the complement would contain a closed point. Over the
algebraically closed base this point gives a rational section of the
representative. Its composite with the normalizer inclusion is a rational
normalizer point, so the assumed membership puts it in the right subgroup,
which is contained in the cell. This contradicts its choice.
Every normalizer-valued test map factors through this representative, so its
entire topological image lies in the cell.

`normalizer_eq_of_rational_points_and_open_cell` then applies the published
all-test open-cell lifting lemma. It lifts the original test map through the
open immersion, writes it as a product of left and right factors, and uses
the all-test separation hypothesis to eliminate the left factor.
The reverse containment is the subgroup's inclusion in its normalizer.

`normalizerPointsEquivOfRationalOpenCell` transports normalizer points through
this equality and then applies the inverse represented-subgroup point
equivalence. Its codomain consists of actual morphisms to the original right
subgroup over the given test scheme, and it preserves multiplication.
The companion `_comp` theorem checks that each lifted morphism composed with
the original inclusion is the original normalizer point.

No reducedness or smoothness hypothesis is imposed on the normalizer
representative or on test schemes. Rational points detect containment in
the **open cell**; they are not used to infer scheme-theoretic containment
in a closed subgroup. The final equality therefore retains nonreduced and
non-affine tests. The proof is derived from the existing representability,
Jacobson, rational closed-point, and open-cell interfaces; it does not
introduce a new external structural theorem.
