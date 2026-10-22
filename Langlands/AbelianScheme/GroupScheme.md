# Group schemes over an arbitrary base

Author: Worker 129.

For an arbitrary scheme `S`, `Langlands.GroupScheme S` is Mathlib's category
`Grp (Over S)` of group objects in the category of schemes over `S`. Its objects
contain the actual multiplication, unit and inverse morphisms with their laws;
its morphisms are morphisms over `S` preserving the group operations. This is the
categorical formulation of Edixhoven–van der Geer–Moonen, Definition (3.1),
printed pp.29–30, including its discussion of homomorphisms and functors of points.

`GroupScheme.points G` is the group-valued Yoneda functor on all schemes over
`S`: at `U` its group is `Hom_S(U,G)`, and restriction is precomposition.
`pointsMap` acts by postcomposition, as recorded by `pointsMap_apply`.
`pointsRepresentableBy` identifies the underlying set-valued presheaf as
represented by the actual object `G.X` of `Over S`. These constructions reuse
Mathlib's group-valued Yoneda functor, rather than storing an arbitrary presheaf.
The correspondence with group schemes and their homomorphisms is
Proposition (3.6), printed p.31 (PDF35).

`GroupScheme.baseChange f` is induced by the actual pullback functor along
`f : T ⟶ S`; the group operations are transported by its cartesian monoidal
structure. This implements the base-change construction in the paragraph
immediately after Definition (3.1), printed p.29 (PDF33).

`GroupScheme.HomAdd G H` is the additive type synonym of the group of
homomorphisms. When `H` is commutative, this has an `AddCommGroup` instance even
if `G` is not commutative. `evalHom G H U x` is the additive map evaluating a
homomorphism at the point `x`; its codomain is `Hom_S(U,H)` in additive notation.
Thus addition comes from multiplication of points in the target. Its zero and
addition laws follow by distributing precomposition through the pointwise group
operations, using Mathlib's monoid-object laws.

`Langlands.CommGroupScheme S` bundles a group scheme with `IsCommMonObj X`.
Its categorical Hom is `Additive (G.toGrp ⟶ H.toGrp)`, with composition inherited
from group-scheme morphisms. `groupHom` removes the additive notation, and `hom`
returns the underlying scheme morphism. The `Preadditive` instance follows from
Mathlib's composition laws for homomorphisms between commutative group objects.
`CommGroupScheme.End G` is `CategoryTheory.End G`, with its induced ring instance:
addition is pointwise addition and multiplication `f * g` is composition
`g ≫ f`. The identity endomorphism is the multiplicative unit. These algebraic
constructions are derived from the group law and distributivity; they do not
assert further geometric theorems from the cited source.

`CommGroupScheme.baseChange` transports commutativity along pullback and defines
a functor on these additive Hom types. Its identity and composition proofs
transfer the corresponding group-scheme functor equalities through
`Additive.ofMul`. The module does not yet assert an additive-functor instance
for base change. It makes no smoothness, properness, connectedness or
abelian-scheme commutativity claim.

Source: B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*,
preliminary version built 2012-02-08, Chapter III Definition (3.1) and its
following base-change paragraph, printed p.29 (PDF33); functor-of-points
discussion and Proposition (3.6), printed pp.30–31 (PDF34–35).
Registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Original retained PDF pages 33–35 were read. No source erratum was present in
the project or published notes at authoring.
