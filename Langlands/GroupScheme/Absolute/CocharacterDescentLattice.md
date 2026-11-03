# Descent on actual cocharacter lattices

Worker 1272.

This derived adapter connects the integral orbit sum in `CocharacterAveraging`
to the actual group-scheme descent construction in `CocharacterDescentGroup`.
The source motivation is the converse of Milne, *Algebraic Groups* (2017),
Theorem 25.1, printed page 544 (PDF page 560): a Galois-invariant cocharacter
obtained by summing its orbit descends to the original field. The explicit
additive-lattice maps and uniqueness packaging are internal consequences of
the preceding modules.

For fields `k` and `K` in the same universe with a `k`-algebra structure on `K`,
`GaloisCocharacterDescent.baseChangeCocharacter` sends an actual group-scheme
cocharacter `Gm_k ⟶ G` to its base change over `K`, precomposed with the inverse
of the canonical `Gm` base-change isomorphism.
`baseChangeCocharacter_injective` proves that this map is injective for every
field extension. It cancels the comparison isomorphism and uses faithful
scheme pullback, and hence faithful pullback on group objects.

If `G` is affine, `K/k` is finite dimensional and Galois, and `ν` is invariant
under the actual geometric transport, `existsUnique_descent` proves that
there is exactly one cocharacter over `k` whose base change is `ν`. The
invariance proof is an explicit parameter of this theorem. Existence is the
constructed `GaloisCocharacterDescent.descend`; uniqueness is the preceding
injectivity result.

For a commutative group scheme `T` over any base scheme `S`, the additive map
`cocharacterLattice.baseChange` extends cocharacters along an arbitrary base
morphism `b : S' ⟶ S`. The theorem `groupHom_baseChange` records that its
underlying group-scheme homomorphism is the usual base change with the same
`Gm` comparison.

Now assume `T` is over `Spec k` and affine, and `K/k` is finite dimensional
and Galois. `cocharacterLattice.descend` takes an element of the actual
cocharacter lattice of `T_K` fixed by
`cocharacterLattice.galoisRepresentation` to the actual cocharacter lattice of
`T`. The invariance premise converts definitionally to invariance of the
underlying group-scheme homomorphism under `transportCocharacter`.
`cocharacterLattice.baseChange_descend` proves recovery in the lattice.

With a `Fintype` structure on `Aut_k(K)`,
`CocharacterAveraging.descendedOrbitSum` applies this descent to the integral
sum of all Galois translates of a given cocharacter `ν` of `T_K`.
`baseChange_descendedOrbitSum` proves that its base change is exactly that
integral orbit sum. There is no division by the Galois-group order.

Finally, `descendedOrbitSum_nonneg_iff` retains the hypotheses of the existing
`galoisOrbitSum_nonneg_iff`. Namely, a family `Φ` of characters of `T_K` is
stable under Galois transport, and the subset of `Φ` pairing nonnegatively with
`ν` is also stable under that transport. For every `χ ∈ Φ`, the theorem proves
that the base change of the descended orbit sum pairs nonnegatively with `χ`
if and only if `ν` does. The proof rewrites the lattice recovery equality and
applies the existing averaging result.

No torus, splitness, smoothness, reductivity, or characteristic hypothesis is
used here. In an application to parabolics, the choice of `Φ` as a root family
and the stability of its nonnegative subset remain separate structural
obligations; this adapter does not assume or prove the parabolic
classification.
