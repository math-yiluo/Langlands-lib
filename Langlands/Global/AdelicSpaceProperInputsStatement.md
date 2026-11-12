# Arithmetic model inputs for proper adelic maps of algebraic spaces

Author: Worker 108.

This module states two intermediate assertions in the proof of Conrad's Proposition 5.8.
It contains proposition definitions and no proofs. Its registered source is Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source locations are printed p.11, proof of Proposition 4.4; p.13, the extension of
Theorem 3.4 to algebraic spaces; and p.17, the paragraph before and statement of
Proposition 5.8, which carries the Proposition 4.4 proof over to algebraic spaces using
Corollary 5.6. These are derived intermediate statements that package those proof steps
using the Library's actual arithmetic rings, spaces and topologies.

`CurvePlaceSpaceProperStagesStatement` concerns a finite constant field `k`, a global
function field `F` with the stated compatible rational-function algebra structure, a
nonempty finite set `S` of places, separated algebraic spaces `X`, `Z` of finite type over
the ring of `S`-integers, and a proper model morphism `g : X ⟶ Z`. For every finite level
`T` above `S`, it asserts both:

- `RingPoints.map g` on points valued in the actual `T`-level, viewed over the `S`-integers,
  is a proper map for the two `curvePlaceSpaceStageTopology` topologies;
- on the full adelic points, the inverse image of the range of the target's `T`-stage map
  is exactly the range of the source's `T`-stage map.

`NumberFieldSpaceProperStagesStatement` asserts these same facts for any number field and
any finite set `S` of finite places. Every level includes every infinite place.
`AdelicSpaceProperStagesStatement` is the conjunction of the two arithmetic cases in an
arbitrary common universe `u`.

The source's level properness step uses Proposition 5.2 to express level points as products
of local point spaces. The local field factors use Corollary 5.6, including archimedean
fields; the integral factors are compact by Corollary 5.7. The exact-preimage step uses the
valuative criterion for properness outside `T` and assembles the local lifts by Proposition
5.2. The equalities here are equalities of actual ranges, so they include the required
existence of a level-valued source point. No injectivity or lifting assertion is being
assumed silently. Properness is the Library's `IsProperMorphism`, which does not require
representability, and topological properness is Mathlib's `IsProperMap`.

`CurvePlaceSpaceProperModelStatement` takes exactly the supplied-model geometric data of
`CurvePlaceSpaceSpreadProperMapStatement`: independent nonempty finite sets `S`, `U`,
separated finite-type models `X`, `Z`, identifications of their generic fibres with `Y`,
`W`, and a proper field morphism `g : Y ⟶ W`. It asserts the existence of a nonempty finite
set `T`, separated finite-type models `M`, `N` over its integer ring, generic-fibre
isomorphisms `eT`, `fT`, and a proper model morphism `gm : M ⟶ N` satisfying
`baseChangeMap (…) gm ≫ fT.hom = eT.hom ≫ g`. The result does not impose a relation between
`T` and the original finite sets; topology independence permits arbitrary replacement
models. Its source is the first paragraph of the Proposition 4.4 proof, using the
algebraic-space extension of Theorem 3.4 on p.13.

`NumberFieldSpaceProperModelStatement` has the same meaning for number fields, allowing
empty finite sets of finite places. `AdelicSpaceProperModelStatement` is the conjunction
of these two cases. Both statements keep the original generic-fibre maps in the commuting
square. The supplied models ensure that `Y` and `W` are separated and of finite type, as
in the published endpoint's finite-type qualification; these assertions claim no extension
to targets merely locally of finite type.

`AdelicSpaceProperInputsStatement` is the conjunction of the stages and model-replacement
statements. The names and this packaging are internal derived content. Together with the
published `AdelicSpacePointTopologyStatement`, these inputs are intended to prove the
unchanged `AdelicSpaceSpreadProperMapStatement`. This module does not assert that proof,
or prove local properness, the valuative criterion, or properness descent.
