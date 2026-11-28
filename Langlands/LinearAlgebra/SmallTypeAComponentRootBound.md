# Root counts for small products of type A components

`SmallTypeAComponentRootBoundStatement` gives at most twenty-two roots for a finite reduced integral root datum with total simple rank at most five, when every Cartan component has type A of rank at most four.

In a numbered component of rank `n`, the signed interval combinations of consecutive simple roots are indexed by the `n(n+1)` ordered pairs of distinct endpoints in `Fin (n + 1)`. The proof checks that the combinations are closed under each simple reflection of the component for `n ≤ 4`. Reflections at vertices of other components act trivially by the zero cross-pairings. Induction by simple reflections puts every actual root in the resulting list, and injectivity of the root map gives the cardinality bound. If one component has rank four, the other ranks sum to at most one. When all ranks are at most three, each component contributes at most four times its rank. These bounds give the claimed maximum of twenty-two.

This supplies the root count for the dimension estimate in Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, §6.6, Theorem 6.26, printed p. 355. [Chapter 6](https://www.sciencedirect.com/science/article/pii/S0079816908620711)
