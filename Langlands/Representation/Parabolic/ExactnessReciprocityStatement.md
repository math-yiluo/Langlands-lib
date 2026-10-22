# Actual block-parabolic exactness and reciprocity

Author: Worker 8. This proposition pair uses the published actual block
construction `Langlands.Group.GL.Blocks`. The assertions are statements with
separate proof obligations.

Fix a prime `p`, a finite extension `F : PadicField p`, a supplied topological
realization `T`, and an ordered positive block shape `B` of total rank `n`.
The field and the three complex representation modules `U`, `V`, `W` occupy
four independent universes. There is no topology on these modules.
Only the actual group topologies induced by `T.topology` are used.

Use the actual matrix groups `G = GL_n(F)`, `P = B.parabolic F.Carrier`
and product Levi `M = B.Levi F.Carrier`. The constructed diagonal projection
`P -> M` has the constructed section `M -> P`. Its kernel `N` is the actual
upper block unipotent radical, normal in `P`.

## Concrete assertions

`Langlands.Parabolic.FrobeniusClause` says that for a smooth representation
`rho` of `G` and a smooth representation `sigma` of `M`, there exists a
complex linear equivalence

`Hom_G(rho, Ind_P^G(inflate sigma)) = Hom_M(J_N rho, sigma)`.

Here `Ind` is the actual **unnormalized** smooth right-translation function
representation, and `J_N` first restricts `rho` to `P`, takes the actual
normal-subgroup coinvariant quotient, and pulls the descended action back
along the Levi section. The equivalence is required to send `f` to the map
`[v] -> f(v)(1)`, using the actual quotient map and function evaluation.
Thus neither side is an arbitrary Hom-space predicate, and the formula fixes
the direction and canonical meaning of the equivalence.

`JacquetExactnessClause` takes a short exact sequence of smooth representations
of this actual `G`, with actual intertwiners `i` and `q`. Its conclusion is
injectivity, image equal to kernel, and surjectivity of the actual coinvariant
maps for `N`. The maps are obtained by restricting `i` and `q` first to `P`
and then to `N`, and applying Mathlib's quotient map construction. They send
`[v]` to `[i(v)]` and `[q(v)]`. The exactness assertion is on underlying
complex linear maps; their quotients carry precisely the Levi actions used
in the first clause. It does not assume that `N` has a compact exhaustion.
That property of the actual unipotent group is part of the eventual proof.

`InductionExactnessClause` takes a short exact sequence of smooth
representations of `M`. It inflates the actual intertwiners along the
diagonal projection, then applies the existing `smoothInducedMap`. Its
conclusion contains all three exactness conditions on those induced maps.
The two local intertwiner constructions retain the original linear maps;
their equivariance fields are proved immediately by evaluating the given
equivariance at the diagonal projection. These are intrinsic constructions,
not assumed theorem conclusions.

`ExactnessReciprocityStatement` is the conjunction of these three concrete
clauses. Smoothness is explicitly assumed for the representations involved.
Neither admissibility nor finite length nor finite dimension is assumed.
Injectivity, surjectivity and equality of linear image and kernel are stated
separately and are not replaced by an arbitrary exactness predicate.

## Original sources and normalization

Bernstein--Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Section 2.3, printed p.446 / PDF p.7, states exactness and first
adjointness of the parabolic induction and Jacquet functors. Its definitions
are in Sections 1.8-1.9, printed pp.444-445 / PDF pp.5-6. Those original
passages were read. Section 2.2 explicitly specializes the standard Levi
groups of `GL_n` to ordered block diagonal products, matching `BlockShape`.

The source uses positive half-modulus covariance for right-translation
induction and the inverse half-modulus on Jacquet quotients. The present
target deliberately gives their unnormalized counterparts. Exactness is
unchanged by these invertible scalar twists. Unnormalized first adjointness
also follows directly: ordinary evaluation reciprocity produces a `P`-map
to the inflated `sigma`; since that target kills `N`, the map uniquely
factors through the relation quotient. Restricting its residual action along
the actual Levi section gives exactly the displayed `M`-map. Conversely,
the decomposition of each element of `P` into its radical and Levi factors
makes that map equivariant for all of `P`. This is a derived normalization
change, not an identification of an arbitrary character with the modulus.

Casselman, Chapter III (April 29, 2019), Section 3, pp.3-4, gives the relation
quotient, its universal property in III.3.2, exactness in III.3.4 and the
evaluation formula in III.3.5. III.3.1 supplies compact exhaustion of actual
p-adic unipotent groups. In the exactness argument, compact averaging proves
the only non-algebraic part, injectivity. The specialization is over complex
coefficients, where averaging finite orbits can divide by their orders;
no assertion over arbitrary coefficient rings is made.

These are genuine `GL_n` specializations of the general reductive source
assertions, over finite extensions of `Q_p`; equal-characteristic local
fields are not covered. The standard empty-block rank-zero case is also
allowed and reduces to representations of the trivial group. No theorem
truth is included in field, subgroup, quotient or representation data.

Original source identifiers and retained files:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.

## Construction dependencies and proof obligations

The pair imports the published actual induction and coinvariant constructions,
smoothness and p-adic group realization modules, together with the published
`Langlands.Group.GL.Blocks` pair. No owner definition is resubmitted here.

The three proposition definitions require separate proofs. Their normalized
versions, the genuine full-modulus identification, transitivity along actual
block refinements, canonical opposite-parabolic duality and full geometric
lemma remain obligations. This pair does not establish the broad task's
completion.
