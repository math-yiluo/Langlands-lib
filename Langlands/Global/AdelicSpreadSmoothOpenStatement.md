# Openness of adelic maps for smooth surjective maps with connected fibres

Author: Worker 105.

`AdelicSpreadSmoothOpenStatement` states Theorem 4.5 of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed p.12, for global fields of both
characteristics. The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the theorem and contains no proof.

Conrad writes: "Theorem 4.5. Let `f : X′ → X` be a smooth surjective `F`-map between separated
`F`-schemes of finite type. If the fibers are geometrically connected then the induced map
`X′(A_F) → X(A_F)` is open." The paragraph before it (printed p.11) gives the counterexamples
`G_m → A^1` and the `n`th-power map, whose fibres are empty or geometrically disconnected.

## The statements

The adelic points and their topologies are the published constructions of
`Langlands/Global/AdelicGenericFiberPoints.lean`: `...AdelePoints K Y` are the actual points
`Spec A_F ⟶ Y`, and `...SpreadAdelePointTopology S X Y e` is Conrad's topology attached to a
finite-type model `X` over the `S`-integers and an isomorphism `e` from its generic fibre to
`Y`.

- `NumberFieldSpreadSmoothOpenStatement`: let `K` be a number field, `Y` and `W` schemes over
  `Spec K` with separated structure morphisms, and `X`, `Z` models over the `S`-integers and
  `U`-integers (finite sets of finite places), locally of finite type and quasi-compact, with
  generic-fibre isomorphisms `e`, `f`. Let `g : Y ⟶ W` be a morphism over `Spec K` whose
  underlying scheme map is smooth (`Smooth`), surjective (`Surjective`) and geometrically
  connected (`GeometricallyConnected`). Then `p ↦ p ≫ g` is an open map (`IsOpenMap`) from
  the adelic points of `Y` to those of `W`, for the topologies attached to `(S, X, e)` and
  `(U, Z, f)`.
- `CurvePlaceSpreadSmoothOpenStatement`: the same for a function field `F` over a finite field
  `k`, with the compatible `RatFunc k`-algebra structure, and finite sets of places.
- `AdelicSpreadSmoothOpenStatement` is the conjunction of the two, in a common universe.

## Relation to the source and derived content

"Separated `F`-schemes of finite type" is formalized by separatedness of `Y` and `W` over the
field. Finite type follows from the existence of the finite-type models. The topologies are
indexed by arbitrary models of source and target, as in the published spread statements such
as `AdelicSpreadFunctorialityStatement` and `AdelicSpreadProperMapStatement`. Conrad's proof
chooses compatible models; the statement claims openness for every choice. The topology does
not depend on the model (published `AdelicSpreadTopologyIndependenceStatement`), so this is
Conrad's claim. "The fibers are geometrically connected" is Mathlib's `GeometricallyConnected`:
every base change along the spectrum of a field is connected. The finite sets of places may
be empty, as in the published spread statements. Global function fields have a finite
constant field, as in `AdelicSpreadProperMapStatement`.

Conrad's proof uses openness of smooth maps on local points, henselian lifting at almost all
places, and the uniform Lang–Weil estimate of his Lemma 4.6, stated separately as
`UniformLangWeilStatement`. Also derived here: the names and the packaging of the two
characteristics.
