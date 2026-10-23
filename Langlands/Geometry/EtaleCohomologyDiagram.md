# Cohomology diagrams over varying schemes

## Scope and variance

Work over a commutative ring `R : Type u`, with schemes in `Scheme.{u}` and
module carriers in universe `u`. The indexing category has independently
specified object and morphism universes:
`J : Type v`, `[Category.{w} J]`.
The input is an actual functor `S : J ⥤ Scheme.{u}ᵒᵖ`, together with an
étaleness instance for every underlying scheme morphism `(S.map a).unop`.
For `a : i ⟶ j`, write

\[
X_i=(S(i))^{\mathrm{unop}},\qquad f_a:X_j\longrightarrow X_i.
\]

Thus restriction of sheaves and pullback on cohomology both go in the direction
`i ⟶ j`. A covariant scheme tower `T : L ⥤ Scheme` can provide the scheme
diagram `T.op`, indexed by `Lᵒᵖ`, once its morphisms are proved étale.
This module does not supply that scheme tower.

## Equality transport and coefficient maps

`restrictionCongr R h` identifies restriction functors for equal scheme
morphisms `h : f = g`. It is constructed by equality elimination, reducing to
the identity isomorphism. `cohomologyMap_congr` proves that composing pullback
along `f` with cohomology of this identification gives pullback along `g`.
Its proof eliminates the equality and simplifies identities.

For `f : Y ⟶ X`, `g : Z ⟶ Y`, coefficient maps
`α : f*F ⟶ G` and `β : g*G ⟶ H`, and every `q : ℕ`,
`cohomologyMapWithCoefficients_comp` proves that the two successive
cohomology maps equal the map along `g ≫ f` with coefficient morphism

\[
(g\mathbin{\gg}f)^*F
 \xrightarrow{c^{-1}}g^*f^*F
 \xrightarrow{g^*\alpha}g^*G
 \xrightarrow{\beta}H.
\]

Here `c` is the published `restrictionComp` identification. The proof uses the
published cohomology composition law, cancels `c` with its inverse, and applies
naturality in the coefficient sheaf.

## Compatible coefficient diagrams

`diagramRestriction R S a` is the published restriction functor for `f_a`.
`diagramRestrictionId` combines equality transport from `S.map_id` with
`restrictionId`. `diagramRestrictionComp` combines `restrictionComp` with
equality transport from `S.map_comp`; its direction is

\[
f_b^*f_a^*\ \cong\ f_{a\mathbin{\gg}b}^*.
\]

`diagramCohomologyMap_id` and `diagramCohomologyMap_comp` transport the published
all-degree pullback laws through these identifications. Their proofs use the
corresponding restriction and cohomology identities; composition follows by
postcomposing the published law with the equality-transport map.

`CoefficientDiagram R S` consists of actual module sheaves `F_i` on the genuine
small étale sites of `X_i` and actual morphisms
`α_a : f_a* F_i ⟶ F_j`. Its two input compatibility laws are sheaf equations:

- `α_id` is `diagramRestrictionId.hom` at `F_i`.
- If `c_ab` denotes `diagramRestrictionComp.hom` at `F_i`, then
  `c_ab ≫ α_(a ≫ b) = f_b*.map α_a ≫ α_b`.

These laws describe compatible coefficients. They do not postulate
cohomology objects, cohomology transition maps, or their functoriality.
The transition maps need not be isomorphisms.

## Constructed cohomology diagram

For a compatible coefficient diagram `D` and `q : ℕ`,
`CoefficientDiagram.cohomology D q` is a functor `J ⥤ ModuleCat.{u} R`.
Its object at `i` is the already constructed right-derived global-section
module `H^q(X_i,D.obj i)`. Its map for `a : i ⟶ j` is

\[
H^q(X_i,F_i)\longrightarrow H^q(X_j,f_a^*F_i)
 \xrightarrow{H^q(\alpha_a)}H^q(X_j,F_j).
\]

The identity field uses the coefficient identity equation and
`diagramCohomologyMap_id`. The composition field first rewrites direct pullback
as successive pullbacks using `diagramCohomologyMap_comp`, then uses the sheaf
composition equation and naturality of pullback in the coefficient sheaf.
Both functor laws are proved for every degree.

## Provenance and remaining specialization

This is internal categorical infrastructure derived from
`EtalePullback`, `EtaleDerivedPullback`, and
`EtaleDerivedPullbackFunctoriality`. Those modules construct the restriction
functors, actual derived cohomology modules, and pullback maps reused here.
The present module adds equality transport, the definition of compatible
varying-scheme coefficients, and their cohomology diagram. It asserts no
named theorem from the literature and introduces no additional axioms.

The earlier `EtaleDerivedSections.diagramFunctor` concerns diagrams of
coefficient sheaves on one fixed scheme; it does not provide this varying-scheme
construction. The new construction is ordinary cohomology with fixed scalar
ring. It does not construct compact support, a trace or Hecke operator,
analytic sites, scalar change, a category of coefficient diagrams, or a
comparison with the separate scheme-automorphism action construction.
The actual Shimura scheme tower and its compatible coefficient morphisms
remain inputs to be constructed before applying this module to Harris.
