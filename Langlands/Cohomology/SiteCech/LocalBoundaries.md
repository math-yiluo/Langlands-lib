# Local boundaries in exact complexes of module sheaves

Author: Worker 512. This internal construction combines the section-representing
free module sheaf from `FreeSections` with Mathlib's kernel and local-surjectivity
APIs. It isolates the local lifting step needed in a future Čech-to-derived
comparison; it is not itself an acyclicity criterion.

Let C be a category, J a Grothendieck topology, and R a commutative ring in
Type w. Assume module sheafification and that C is locally small in w. For a
short complex S of R-module sheaves and a section s of its middle term over U
killed by its second arrow, `cycleSection` is a section of the cycle sheaf
mapping to s. To construct it, the free-representable section equivalence
turns s into a sheaf morphism. Naturality in the coefficient sheaf shows that
this morphism is killed by the second arrow. Its kernel lift corresponds to
the desired cycle section. `cycleSection_i` proves the stated image identity.

The remaining results additionally assume
`J.WEqualsLocallyBijective (ModuleCat R)`: module sheafification equivalences
are exactly locally bijective presheaf morphisms. Under this explicit
compatibility assumption, Mathlib identifies epimorphisms of module sheaves
with locally surjective morphisms.

If S is exact, its map from the first term to the cycle sheaf is an
epimorphism. The covering image sieve for `cycleSection` is contained in
the image sieve of s under the first arrow of S. This follows from the
factorization of that arrow through the cycle sheaf, naturality of the
cycle inclusion, and `cycleSection_i`. Upward closure of J therefore proves
`imageSieve_mem_of_exact`: on a covering sieve, s has local preimages under
the first arrow.

`imageSieve_mem_of_injectiveResolution` applies this result to the three
consecutive terms in degrees n, n+1, n+2 of an injective resolution, using
Mathlib's positive-degree exactness theorem. Thus every positive-degree
cocycle section of that resolution becomes a boundary on a covering sieve.

There are no products, pullbacks or subcanonical assumptions on C, nor is
there a compactness assumption. This unit supplies no finite compact
refinement, no vanishing of Čech cohomology, no identification with a
Čech complex, and no vanishing of derived sections on restricted
equivariant injectives. Those are separate obligations in the analytic
comparison proof.
