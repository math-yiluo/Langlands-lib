# Universal rigidified line bundles

For a scheme map `f : X → S` with section `ε` and section equation, and an
`S`-scheme `P`, take an actual rigidified line bundle `L` on `P ×_S X`.
`classOf L` is its class in the quotient by compatible rigidified
isomorphisms. `classifyingMap L T` sends an `S`-map `h : T → P` to the class
of the actual relative pullback of `L` along `h`.

`IsUniversal L` is the proposition that this specified map is bijective
for every `S`-scheme `T`. It has no coherence proof parameter: the quotient
and the individual pullback maps are already defined without one.
`classifyingMap_eq_iff` unfolds equality of quotient classes into existence
of a compatible rigidified isomorphism. Using this equivalence and quotient
induction, `isUniversal_iff` proves that the predicate is precisely the
following universal property: for every rigidified line bundle `M` on
`T ×_S X`, there is a unique `S`-map `h : T → P` for which `h*L` is
isomorphic to `M` as a rigidified line bundle. The unique object here is the
map `h`; no uniqueness of the bundle isomorphism is asserted.

`classifyingEquiv` constructs the classification equivalence from this
bijectivity proof. With the explicit hypothesis
`coherence : RigidifiedModule.PullbackCoherenceStatement`, the two elementary
laws `classifyingMap_comp` and `classifyingMap_id` follow from the functor
laws of the actual `classPresheaf` by evaluation at `classOf L`.
`representableBy` then constructs Mathlib's
`Functor.RepresentableBy` for that presheaf. Its hom equivalence is exactly
the pullback classification equivalence, and its naturality is the
composition law just described. Mathlib's universe-polymorphic
`RepresentableBy` accommodates the value universe `Type (u + 1)` directly.

For two bundles satisfying this predicate, `comparisonIso` applies
Mathlib's `RepresentableBy.uniqueUpToIso` to these constructed
representations. This constructs an isomorphism of their representing
`S`-schemes. The separate statement that exactly one isomorphism has the
required compatibility with the universal bundles is left to the
uniqueness statement and proof unit.

The original reference is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
Chapter VI §1, (6.2), printed p.88 (PDF p.92), especially the paragraph
defining the universal rigidified line bundle, called the Poincaré bundle.
The retained source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source writes `X ×_S T`; the construction uses the canonically
symmetric product `T ×_S X` from `RelativeGeometry`. Reversing the direction
of the bundle isomorphism does not change its existence.

This is a derived categorical construction of the universal-property
predicate and its representability bridge. The source's additional
quasi-compactness, quasi-separatedness and universal structure-sheaf
pushforward hypotheses are not needed to formulate this predicate or to
deduce representability from it. They are not used here to assert
existence of a universal bundle, uniqueness of bundle automorphisms,
an abelian group law, or comparison with the fppf Picard sheaf.
The canonical pullback coherence proposition remains an explicit
hypothesis for the representation and comparison constructions.
