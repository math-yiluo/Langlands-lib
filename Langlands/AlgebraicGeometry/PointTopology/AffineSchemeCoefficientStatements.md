# Coefficient change on actual affine scheme points

Author: Worker 105.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 2.2, printed page 3, and its use of Proposition 2.1,
printed page 2. Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module supplies Prop-valued statements; it does not prove them.

R is any commutative coefficient ring. S and T are commutative R-algebras
with specified topologies. Rings and schemes share one arbitrary universe.
The point sets are actual relative scheme morphisms from Spec S or Spec T
to X over Spec R. Their topology is the published global-section evaluation
topology. For f : S → T, `RingPoint.changeRing f` is actual precomposition
with Spec f, so its direction is from S-valued to T-valued points.

`AffineSchemeCoefficientContinuityProperty` states continuity of this point
map whenever f is continuous. `AffineSchemeCoefficientEmbeddingProperties`
states that an embedding, or a closed embedding, of coefficient algebras
induces the corresponding kind of point embedding. These three assertions
hold for every affine X, without finite type, Hausdorffness, or continuity
of ring operations. This extension of the source is derived: under the
actual affine point comparison the map is composition of algebra
homomorphisms with f; its topology is controlled by all evaluations.
For a closed coefficient image, requiring every evaluation to lie in that
image is an intersection of closed conditions.

`AffineSchemeCoefficientOpenProperty` separately assumes topological rings
S and T and that X is locally of finite type over Spec R. As X is affine,
its coordinate algebra is of finite type. If f is an open embedding, the
point map is an open embedding: belonging to its image can be checked on
finitely many algebra generators. `AffineSchemeDiscreteProperty`
separately states that such finite-type affine points over a discrete
topological value ring are discrete. Together with the coefficient
embedding assertion, this also handles a discrete subring embedded in T.
No topology on R or continuity of its structure maps is required.

The ring inclusion in Example 2.2 is reversed in the printed phrase
“if R′ is closed (resp. open) in R.” The correctly oriented assertion is
that R is closed or open in R′. Our f goes from S to T and the hypotheses
are closed or open embeddings of S into T. Specializing the coefficient
ring and S to R recovers that assertion for actual affine scheme points.
The comparison with actual points of the base-changed scheme is a separate
published interface; it is not assumed by these statements.

`AffineSchemeCoefficientProperties` combines the assertions with their
individual hypotheses. The adelic and DVR instances of Example 2.3 and the
finite locally free Weil restriction of Example 2.4 remain separate
obligations.
