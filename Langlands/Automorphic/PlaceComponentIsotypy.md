# Isotypy of cuspidal realizations at an infinite place

At a real or complex place, an actual cuspidal operator realization is spanned by the
images of the intertwiners from any one of its irreducible place-stable subspaces.
The two theorems use `Archimedean.IsGKIsotypic` for this spanning condition.

The canonical projection to the zero-denominator subquotient is a linear equivalence
intertwining the compact and complexified Lie actions at the place. It maps the given
irreducible stable subspace onto an irreducible stable subspace of that subquotient.
The two `OperatorSubquotient.isRealPlaceIsotypic_restrict` and
`OperatorSubquotient.isComplexPlaceIsotypic_restrict` theorems give the spanning result
there. Composition with the restriction of the projection on the source and the
inverse projection on the target takes those intertwiners back to the original
realization. Surjectivity on both carriers transports the span.

This is a derived form of the subquotient results. The isotypy argument underlying
those results comes from Flath, *Decomposition of representations into tensor
products*, proof of Theorem 1, p. 180 (PDF p. 176), and the formulation for
archimedean modules in Theorem 3 and its discussion, pp. 181–182 (PDF pp. 177–178),
registered as `flath-1979-tensor-products`.
