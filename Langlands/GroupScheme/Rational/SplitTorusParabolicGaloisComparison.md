# Galois comparison for the parabolics of a split maximal torus

Let `F → K → E` be a tower of fields and let `M` be an affine group over `F`.
Consider a split pinning `q` of `M_K` and Galois pinning data `p` for `M` over
`E`. The latter give a torus over `F` with a split pinning over `E`.

`exists_rootDatumEquiv_parabolic_galoisComparison` identifies their root data
by a single equivalence. Its forward map on cocharacters is
`e.coweightEquiv.symm`. For each Weyl element of the root datum of `p`, the
corresponding change of cocharacter for `q` conjugates the parabolic by a
`K`-point. For each pair of automorphisms `σ` of `K/F` and `τ` of `E/F` with
`τ` restricting to `σ`, the parabolic transported by `σ` equals the parabolic
of the `τ`-transported cocharacter up to a Weyl element and conjugation by a
`K`-point. The action of `τ` on cocharacters is
`cocharacterLattice.galoisRepresentation F E p.torus τ`. Each point and Weyl
element can be chosen uniformly for all cocharacters.

The equivalence is induced by base change and conjugacy of the split maximal
tori over `E`. The split Weyl-group theorem realizes Weyl elements by
normalizer points over `K`. For the transport assertion, first conjugate the
torus transported by `σ` back to the torus of `q` over `K`. Over `E`,
the commuting-square pullback comparison identifies the torus transported
before base change with the torus transported by `τ` after base change.
Two conjugators then carry this torus to the torus of `p`. The first uses the
`K`-conjugator and then the original comparison over `E`, and the second
transports the original comparison along `τ`. Their quotient normalizes
the torus of `p`. Its action on the cocharacter lattice supplies the Weyl
element. The cocharacter pullback law transports the equality back to the
parabolic calculation over `K`.

`galoisAction_mem_weyl_of_fixes` also assumes that `M` is locally of finite
type. When `τ` fixes `K`, it acts trivially on the lattice of the split
torus of `q` over `K`. Independence of the star action and its compatibility
with scalar extension give the trivial star action of `τ` on `p`. This is
equivalent to membership of the ordinary Galois action in the Weyl group.

These comparisons make explicit the passage between a split maximal torus
over a cubic field and the absolute diagram action in the cyclic trialitarian
parabolic construction of Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), §6.8, printed pp. 371–372. The comparison itself uses no
trialitarian type or degree condition.
