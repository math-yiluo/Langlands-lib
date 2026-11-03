# Fixed vectors of represented fppf-local products

This internal derived module works over any commutative ring `R : CommRingCat.{u}`
with the published finite-coordinate `MatrixRepresentation` and its unchanged
all-test predicate `IsFixedVector`. The coordinate type `n : Type` is finite
with decidable equality; it need not be nonempty. No smoothness, connectedness,
affineness, normality, or field assumption is required.

`IsFixedAt ρ x v` is the existing fixed-vector coordinate equation on one
specified relative point `x`; it introduces no new action or notion of global
fixedness.

`isFixedVector_iff_epi_point` says that one test point `x : T ⟶ G.X`
whose underlying scheme map is epimorphic detects whether a coefficient vector
is fixed on every relative scheme test. The forward implication specializes
the definition. For the reverse implication, the proof pulls back the
universal-point equation along `x`. Naturality of the representation's
matrices, naturality of `scalarMap`, and preservation of matrix-vector
multiplication by a ring homomorphism identify that pullback with the supplied
equation. Injectivity on global sections for scheme epimorphisms reflects each
coordinate equality. The existing universal-point criterion then gives fixedness
on every test scheme.

`isFixedVector_restrict_fppfProduct` assumes actual homomorphisms
`j : H ⟶ G`, `l : U ⟶ G`, and `i : P ⟶ G`, representations
`hH : F.IsRepresentedBy j` and `hU : N.IsRepresentedBy l`, and the published
predicate `hi : SubgroupFunctor.IsFppfProduct F N i`. If a vector is fixed
by both restrictions of a representation of `G` to `H` and `U`, it is fixed
by its restriction to `P`. The published multiplication map
`hi.productMul hH hU : H.X ⊗ U.X ⟶ P.X` is an epimorphism of schemes.
Its composite with `i` is the ordered product of the two universal factor
points. Since the representation preserves multiplication, the resulting matrix
fixes the vector by the two supplied fixedness equations. The preceding
epimorphic-test criterion descends that equation to `P`.

The provenance is entirely internal: the proofs combine
`Reductive.UnipotentQuotient`, `SubgroupFunctor.FppfProductGeometry`, matrix
multiplication identities, and the imported injectivity theorem for global
sections. The multiplication map is used only as a scheme morphism, and no group
homomorphism property is needed. The module neither constructs a represented
product nor proves unipotence or existence of a radical; constructing a common
nonzero fixed vector remains a separate obligation for the unipotence argument.
