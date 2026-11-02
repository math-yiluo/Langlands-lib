# Minus-one scalar of an ordinary two-block Jacquet realization

This internal development derives the minus-one scalar for an actual ordinary
Jacquet realization from the scalars of its two block coefficient models.
The tensor contraction scales by the product of these block scalars.
The block diagonal negative identities give the ambient negative identity;
the positive Levi modulus of this element is one because its square is one.
Normalized lower-induction covariance therefore gives the corresponding
scalar-section law. Integrating it gives the ordinary Jacquet law for the
same supplied rectangular measure, and model-map surjectivity gives the
minus-one scalar on the entire induced coefficient model.

`JacquetCentralScalarLaw` packages the conclusion for every rectangular measure
and every functional satisfying the displayed ordinary Jacquet realization.
`jacquetCentralScalarLaw` proves it under the two block scalar hypotheses.
There are no Whittaker-type, functional nonvanishing or integrability assumptions;
the measure is preserved throughout. This is an internal deduction from the
published tensor, block embedding, normalized lower-induction and Jacquet
function definitions. It asserts no gamma multiplicativity or final dominant-rank
analytic base.
