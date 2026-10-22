# Natural normalized transitivity for actual block refinements

Author: Worker 8.

Let `F` be a finite extension of `Q_p`, with compatible topological data
`T`, let `B` be an ordered positive block shape of rank `n`, and let `S`
refine each block of `B`. Write `G = GL_n(F)`, `M = B.Levi F.Carrier`,
and `L = refinedLevi F.Carrier B S`. The inner parabolic and radical are
the actual subgroups of `M` defined by `S`. The direct smaller parabolic
and its full radical are their preimages through the outer block
projection, as constructed in `RefinementComposition`.

All three induction and all three Jacquet functors in this statement
are constructed from these actual groups. Each uses the explicit
determinant-norm modulus and its canonical positive square root.
The direct full modulus is the product of the restriction of the
outer modulus to `L` and the inner modulus. The imported composition
module proves the corresponding positive and inverse-half product
identities and the factorization of the outer character through the
inner projection.

## Induction

`NormalizedRefinementInductionTransitivityClause` asserts a natural
isomorphism

`i_M^G ∘ i_L^M ≅ i_L^G`.

The Lean functor composition `inner ⋙ outer` applies the inner functor
first. On each actual smooth `L`-representation the forward map is fixed
by the formula

`E(F)(g) = F(g)(1_M)`.

The inverse is also prescribed:

`E⁻¹(f)(g)(m) = δ_B(m)^(-1/2) f(B.leviEmbedding(m) * g)`.

Here `δ_B^(1/2)` is exactly `T.leviHalfModulus B`. Its inverse is necessary
because the outer induced functions have covariance with positive half
modulus and the action is right translation. The inner function space
has covariance with the inner positive half. The formulas use
`Induction.eval` on those actual spaces, and the isomorphism components
are actual equivariant linear maps in the canonical smooth categories.

## Jacquet

`NormalizedRefinementJacquetTransitivityClause` asserts a natural
isomorphism

`r_L^M ∘ r_M^G ≅ r_L^G`.

It sends the iterated quotient class of each original vector to its
direct class: `E([[v]]) = [v]`. The first quotient is the published
parabolic-relative `B.JacquetModule`; the second is the ambient inner
radical quotient used by `RefinedJacquetModule`. The target is the
ambient full-radical quotient `ComposedJacquetModule`. Thus the
statement retains the required comparison of these actual quotient
presentations and their normalized Levi actions.

Each `E` is a categorical natural isomorphism, so invertibility,
equivariance and naturality with respect to every smooth-representation
morphism are part of the conclusion. The functors' maps are the actual
postcomposition maps on induced functions and descended maps on
coinvariants. No arbitrary functor, linear-equivalence witness or
normalization compatibility is supplied as a hypothesis.

## Quantifiers and source

The field and carrier universes are independent. The initial carrier
universe is `uV`; direct and iterated induction both land in
`max uF uV`, and all Jacquet functors preserve `uV`. Smoothness is carried
by the objects of the canonical categories. Admissibility, irreducibility,
finite length and finite dimension are not assumed. The harmless empty
block case is included by the actual constructions.

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), ID
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original printed pages 444-446 (PDF pages 5-7) were read directly:
section 1.8 fixes covariance, right translation and inverse-half
Jacquet normalization; Proposition 1.9(c) composes the triples and
requires compatibility of normalizing factors; sections 2.1-2.2
specialize standard Levi chains to ordered block refinements of `GL_n`;
Proposition 2.3(c) gives the two transitivity identities.

The functor identity is interpreted as a natural isomorphism between
the concrete Lean presentations. The evaluation and quotient formulas
are the canonical derived maps for these conventions, rather than
verbatim formulas from the source. The statement uses smooth induction,
the source's capital `I`; Proposition 1.9(c) covers that version directly.
Its coincidence with compact induction for parabolics and the
Haar-scaling interpretation of the explicit modulus remain separate
obligations. These declarations are proposition-valued proof targets,
and this module proves neither transitivity assertion.
