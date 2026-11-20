# Bottom-minor shifts from increasing position weights

For a list of nonnegative position weights bounded by `q`, take one set of
rows for each level `t < q`. A position belongs to that set exactly when its
weight exceeds `t`. Thus each row occurs as many times as its weight. The
sets decrease with the level, so the set of smaller cardinality in any pair
is contained in the other. If the weights increase with the row index,
every set is a bottom segment.

The diagonal factor of the product of those minors is the product of the
corresponding coordinate powers. For a principal-series list with the
prescribed parities, subtracting the weights from the exponents and taking
even signs gives a list whose character times this factor equals the
original character. This is the shift needed by `RealBottomMinorProducts`.
The construction uses the same upper level sets as `RealCompactRows` and
the sign and exponent calculation of `RealTiedMinorProduct`.
