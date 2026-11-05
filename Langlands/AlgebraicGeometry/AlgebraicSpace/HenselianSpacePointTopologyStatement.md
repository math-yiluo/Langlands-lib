# The topology on rational points of algebraic spaces over henselian fields

Author: Worker 105.

`HenselianSpacePointTopologyStatement` states the topological part of
Proposition 5.4 of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp.14–15. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
only states the result and contains no proof.

Conrad's Proposition 5.4 (printed p.14) reads: "Let `k` be a henselian valued
field, and `X` a (quasi-separated) algebraic space locally of finite type over
`k`. There is a unique way to topologize `X(k)` so that the following properties
hold: it is functorial, compatible with fiber products and the case of schemes,
open (resp. closed) immersions in `X` are carried to open (resp. closed)
embeddings in `X(k)`, and étale maps are carried to local homeomorphisms." It
continues on printed p.15: "If `X` is separated then the topology on `X(k)` is
Hausdorff, and it is totally disconnected (resp. locally compact) when `k` is
non-archimedean (resp. locally compact)."

## Objects

Throughout, `K : Type u` is a nontrivially normed field and the algebraic spaces
are the Library's actual algebraic spaces
`X : AlgebraicSpace (Spec (CommRingCat.of K))` from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`. Such a space is an fppf
sheaf on schemes over `Spec K` with representable diagonal and a surjective étale
scheme atlas. The following existing Library notions are used.

- `RingPoints K X K` (from `RingPoints.lean`) is the set `X(K)`: the sections of
  `X` over the actual `Spec K` with its identity structure map.
  `RingPoints.map f` is the map `X(K) → Y(K)` induced by a morphism
  `f : X ⟶ Y`.
- `schemeRingPointsEquiv K U K` identifies the `K`-points of the space
  `(schemeToSpace _).obj U` of an actual scheme `U` over `Spec K` with the
  relative scheme points `RingPoint K U K`, the morphisms `Spec K ⟶ U` over
  `Spec K`. Those carry the Library's `schemePointTopology K U K`, the final
  topology from the affine open charts built from the norm topology of `K`.
- `IsQuasiSeparated X` says that the diagonal of `X` is representable with
  quasi-compact represented projections. `IsSeparated X` says that the diagonal
  is a representable closed immersion. Both are from `RingPoints.lean`.
- `LocallyOfFiniteTypeOverBase X` (from `StructuralAtlasGeometry.lean`) says that
  `X` has a surjective étale atlas by a scheme locally of finite type over
  `Spec K`.
- For a morphism `f` of algebraic spaces, `hom f` is its underlying
  transformation of presheaves. `IsOpenImmersion (hom f)` and
  `IsClosedImmersion (hom f)` are the Library's representable versions: every base
  change of `hom f` to an actual scheme is represented by a scheme morphism with the
  property. Open and closed immersions of algebraic spaces are representable by
  definition, so these are the usual notions. For a transformation `φ` out of the
  functor of points of an actual scheme, the Library's `IsEtale φ` likewise means
  representable with étale represented projections. Maps from schemes to algebraic
  spaces are always representable.
- `IsHenselianValuedField K` is the henselian condition published with Lemma 5.3
  in `Langlands/AlgebraicGeometry/PointTopology/HenselianEtalePointStatement.lean`:
  the norm of `K` extends uniquely to an absolute value on every algebraic
  extension field. This is Conrad's definition on printed p.14 ("a valued field is
  a field `k` equipped with a nontrivial absolute value, and it is henselian if
  this absolute value uniquely extends to every algebraic extension").

## Definitions and the statement

- `IsEtaleMorphism f`, for a morphism `f : X ⟶ Y` of algebraic spaces over any
  scheme `S`, says: for every actual scheme `U` over `S` and every
  `φ : (schemeYoneda S).obj U ⟶ X.presheaf` with `IsEtale φ`, the composite
  `φ ≫ hom f` satisfies `IsEtale`. This is the Stacks Project definition of an étale
  morphism of algebraic spaces (registered source
  `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, Properties of Algebraic
  Spaces, Definition 16.2, Tag 03FR): "A morphism `f : X → Y` between algebraic
  spaces over `S` is called étale if and only if for every étale morphism
  `φ : U → X` where `U` is a scheme, the composition `f ∘ φ` is étale also." It does
  not require `f` to be representable by schemes. For example, an étale morphism from
  an algebraic space that is not a scheme to a scheme is never representable. Stacks
  Algebraic Spaces, Example 14.2 (Tag 03FN, registered source
  `stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05`) gives a quasi-separated
  space of finite type over a field with such an étale map to the affine line.
- `IsQuasiSeparatedLocallyFiniteType K X` is
  `IsQuasiSeparated X ∧ LocallyOfFiniteTypeOverBase X`. These are the spaces of
  Proposition 5.4.
- `IsAdmissibleRationalPointTopology K τ` is a property of a family `τ` assigning
  a topology `τ X` on `RingPoints K X K` to every algebraic space `X` over
  `Spec K`. It is the conjunction of six clauses, each required only for spaces
  satisfying `IsQuasiSeparatedLocallyFiniteType K`:
  1. functoriality: for every morphism `f : X ⟶ Y`, the map `RingPoints.map f`
     is continuous from `τ X` to `τ Y`;
  2. the case of schemes: for every actual scheme `U` over `Spec K`, the
     bijection `schemeRingPointsEquiv K U K` is a homeomorphism from
     `τ ((schemeToSpace _).obj U)` to `schemePointTopology K U K`;
  3. fibre products: for every commutative square of morphisms
     `p' : P ⟶ X'`, `p'' : P ⟶ X''`, `f' : X' ⟶ X`, `f'' : X'' ⟶ X` whose
     underlying presheaf square is a pullback (`IsPullback (hom p') (hom p'')
     (hom f') (hom f'')`), the map `w ↦ (RingPoints.map p' w, RingPoints.map p'' w)`
     is a topological embedding of `τ P` into the product of `τ X'` and `τ X''`;
  4. open immersions: if `IsOpenImmersion (hom f)` for `f : X' ⟶ X`, then
     `RingPoints.map f` is an open embedding;
  5. closed immersions: if `IsClosedImmersion (hom f)`, then `RingPoints.map f`
     is a closed embedding;
  6. étale maps: if `IsEtaleMorphism f`, then `RingPoints.map f` is a local
     homeomorphism.
- `SeparatedRationalPointTopologyProperties K τ` says that for every space `X`
  with `IsQuasiSeparatedLocallyFiniteType K X` and `IsSeparated X`, the space
  `RingPoints K X K` with topology `τ X` is Hausdorff (`T2Space`); it is totally
  disconnected (`TotallyDisconnectedSpace`) if the norm of `K` is ultrametric
  (`IsUltrametricDist K`); and it is locally compact (`LocallyCompactSpace`) if
  `K` is locally compact.
- `HenselianSpacePointTopologyStatement` says: for every nontrivially normed
  field `K : Type u` with `IsHenselianValuedField K`, there is a family `τ` such
  that
  - `IsAdmissibleRationalPointTopology K τ` holds;
  - every family `τ'` satisfying `IsAdmissibleRationalPointTopology K τ'` agrees
    with `τ` on every space `X` satisfying `IsQuasiSeparatedLocallyFiniteType K X`;
  - `SeparatedRationalPointTopologyProperties K τ` holds.

## Relation to the source and derived content

Conrad's "unique way to topologize `X(k)`" refers to a topology on `X(k)` for
every space in his class, subject to conditions that relate different spaces
(functoriality, fibre products, immersions, étale maps). The statement therefore
quantifies over families `τ` indexed by all algebraic spaces over `Spec K`. Only
the values on quasi-separated locally finite type spaces are constrained, and
uniqueness is asserted only for those values. The values of `τ` on other spaces
are irrelevant.

The fibre product clause is equivalent to Conrad's compatibility. In a pullback
square of presheaves, evaluation at `Spec K` gives a pullback square of sets. So
the map `P(K) → X'(K) × X''(K)` is a bijection onto the set-theoretic fibre
product `X'(K) ×_{X(K)} X''(K)`. It is an embedding exactly when it is a
homeomorphism onto that fibre product with the subspace topology of the product
topology, which is the fibre product topology. Requiring the square to be a
pullback, rather than using a chosen fibre product, covers every model of
`X' ×_X X''`. A fibre product of quasi-separated spaces locally of finite type
over `Spec K` is again quasi-separated and locally of finite type, so the
hypothesis on `P` does not restrict Conrad's compatibility.

"Compatible with the case of schemes" is read as clause 2: on the space of an
actual scheme `U`, the topology is the existing scheme point topology, transported
along the canonical identification of points. The scheme `U` is required to give a
space in Conrad's class, namely a quasi-separated space locally of finite type
over `Spec K`.

Quasi-separatedness is Conrad's standing convention for Section 5 (printed p.13):
"We will work with quasi-separated algebraic spaces (as is the case throughout
[Kn])". "Non-archimedean" is formalized as `IsUltrametricDist K`, the
ultrametric inequality for the norm, and "`k` locally compact" as
`LocallyCompactSpace K` for the norm topology. The extension fields in
`IsHenselianValuedField K` range over the universe of `K`; the Markdown of the
Lemma 5.3 statement explains why this does not weaken the condition.

Conrad's proof (printed p.15) justifies the separated-space properties as
follows: "For separated `X` the Hausdorff property of `X(k)` is a formal
consequence of the desired compatibility with closed immersions and fiber
products, and the assertions concerning local compactness and total
disconnectedness are also clear via the scheme case when `X` is separated." The
statement asserts these properties for the family `τ` produced by the existence
part. By uniqueness, they then hold for every admissible family.

Also derived here: the names of the predicates, the packaging of the six clauses
into one admissibility predicate, the use of `hom f` with the Library's
representable open and closed immersion properties, and the formulation of
`IsEtaleMorphism` through the Library's `IsEtale` for maps out of schemes.

## Not stated here

- The third paragraph of Proposition 5.4, on the unique functorial `k`-analytic
  manifold structure on `X(k)` for smooth `X` over complete `k`, is not part of
  this statement.
- Conrad's proof cites [Kn, II, Thm. 6.4] for lifting each `x ∈ X(k)` to a
  `k`-point of a scheme étale over `X`. That input is stated separately as
  `RationalPointEtaleLiftStatement` in
  `Langlands/AlgebraicGeometry/AlgebraicSpace/RationalPointEtaleLiftStatement.lean`.
  The construction of the topology as the strongest one making all maps
  `U(k) → X(k)` continuous, for schemes `U` étale over `X`, is proof material.
- Lemma 5.3, used throughout the proof, is the published
  `HenselianEtalePointLocalHomeomorphStatement`.
