# Character selection on actual translated function spaces

Take an algebra acting on a coefficient space and an abelian group translating its evaluated functions. Suppose the coefficient action descends to the span of translated functions, each original function has a finite-dimensional translation orbit, and a surjection onto a simple module kills the kernel of the original evaluation.

The translate at the identity embeds the original image into the larger space of translated functions. Its kernel lies in the kernel of the given surjection, so its range still surjects onto the same simple module. Since translation commutes with the coefficient action, it acts by linear endomorphisms over the original operator monoid algebra. Every vector has a finite-dimensional translation orbit. Applying the finite-orbit version of Langlands's Lemma 6 to the range and its surjection gives a cyclic submodule whose generator transforms by a character and which still surjects onto the same simple module.

`exists_translatedFunction_centralCyclicQuotient` is the function-space form of this selection argument for Task 6823. The algebraic character step follows Langlands, *On the notion of an automorphic representation* (1979), Lemma 6, printed p. 205.
