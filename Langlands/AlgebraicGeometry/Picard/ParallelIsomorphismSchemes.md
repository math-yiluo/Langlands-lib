# Smooth schemes of parallel Picard isomorphisms

This is an internal consequence of the actual smooth relative automorphism
hypothesis. For actual endpoint maps `a,b : T → U`, the presheaf
`parallelIsomorphismPresheaf` retains every actual isomorphism between the
pullbacks of the family along these endpoints, on the entire slice of
schemes over `T.left`.

The comparison assumes an actual isomorphism `e` between the two endpoint
pullbacks over `T`. `parallelAutomorphismComparison` first uses the
pseudofunctor composition comparison to identify automorphisms of the
pulled-back source family with the source automorphism presheaf
precomposed along `a`. It converts morphisms to actual isomorphisms in
the Picard groupoid and applies the natural parallel-isomorphism torsor
comparison given by `e`. The same iterated-slice functor and universe
lift as in the actual relative automorphism definition are used.

`exists_parallelIsomorphismScheme` applies smooth automorphism
representability to the actual source pullback family and transports its
whole presheaf representation through this comparison. The resulting
scheme is smooth over `T.left`. The hypothesis `e` is essential here:
this construction is intended for the endpoint kernel over the actual
arrow scheme, where its universal actual arrow supplies `e`. It does not
choose an arrow between arbitrary endpoint pullbacks or prove a quotient
assertion.
