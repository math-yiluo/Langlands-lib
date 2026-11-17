# Rapid decay in the archimedean simple roots

These internal estimates extend the Library's finite trace-frequency argument
from rational rows to arbitrary elements of the mixed archimedean space. They
then combine it with the normalized simple-root moment estimate in the companion
helper module. They assert no adelic gauge construction or convergence theorem.

`exists_norm_le_sum_mixedTrace_mul` says that, for a nonzero rational character
parameter, the mixed-space norm is bounded by a constant times the sum of the
absolute trace frequencies along the lattice basis. Multiplication by that
parameter is invertible, and the published mixed trace pairing is injective.
The finite-dimensional norm bound for an injective linear map applies to their
composition. This argument works for every mixed-space element, without any
rationality hypothesis.

`exists_simpleRoot_row_decay_of_detPower` assumes that every vector in the
Whittaker decay class has a bound with the same determinant exponent. For a
fixed vector, standard additive character, compact set of right factors and
natural number `N`, it bounds the Whittaker norm times
`(1 + ‖(d_i / d_(i+1))_i‖)^N` by a constant times that determinant power.
The bound is uniform in the point with archimedean diagonal `d` and in the
compact right factor. Rank zero and derivative order zero are included.

The proof writes the character using its nonzero rational parameter. Trace
frequencies along the finitely many lattice basis directions detect the norm of
the whole simple-root row. The normalized moment theorem bounds the `N`th power
of each frequency times the Whittaker norm. Applying a finite-sum power
inequality, with an extra index for the constant term, and adding the
zeroth-order Whittaker bound proves the result. All estimates retain the
specified determinant exponent. Finite-place support and construction of a
Schwartz–Bruhat majorant remain separate obligations.
