# Natural graded functors under precomposition

Worker 593 adds natural graded comparisons and gluing interfaces to the existing
`RepFunctorFiltration.precomp` construction in `Filtration.Transport`. This is
an internal transport of already constructed filtration data.

Let `R` be a commutative ring, `G` a group, `C,D` categories,
`F : C ⥤ Rep R G`, `s : RepFunctorFiltration F n`, and `J : D ⥤ C`.
The existing precomposition evaluates each actual step at `J.obj X` and each
restricted map at `J.map f`, keeping the same finite indices, monotonicity and
zero/full endpoints.

`RepFunctorFiltration.precompGradedIso s J i` identifies the actual quotient
functor `(s.precomp J).graded i` with `J ⋙ s.graded i`. On objects, both are
the quotient of the same upper subrepresentation by the same pullback of the
lower one. On morphisms, both use the same restricted map `F.map (J.map f)`
descended by `Submodule.mapQ`. The complete functors are definitionally equal,
so `eqToIso (by rfl)` gives the natural isomorphism. No objectwise choice or
additional quotient comparison is required.

`RepFunctorFiltration.HasGradedPieces.precomp` takes supplied natural
identifications `s.graded i ≅ pieces i`, whiskers them on the left by `J`, and
composes them with `precompGradedIso`. Thus every actual grade of the
precomposed filtration is naturally isomorphic to `J ⋙ pieces i`.
`HasOrderedFiltration.precomp` uses this construction on the witnessing
filtration. `IsGluedFrom.precomp` retains the original witnessing permutation
of `Fin n` and applies the ordered result. The family still has exactly `n`
entries: repeated steps, zero grades and distinct indices carrying isomorphic
representations all remain present.

The ring, group, representation carrier and the objects and morphisms of both
source categories have independent universes. The construction uses no
topology, smoothness, dimension, length, irreducibility or positivity premise.
It applies to every natural `n`, including `n = 0` whenever a zero-length
filtration has already been supplied. It does not assert that arbitrary
functors possess a zero-length or any other filtration.

## Provenance and dependencies

Provenance is internal and source-free. The only mathematical inputs are the
published actual subfunctor, successive-quotient and filtration definitions,
their existing precomposition construction, definitional equality of these
quotient functors, and composition and left whiskering of natural
isomorphisms. No representation-theoretic theorem supplies a step.

The sole direct project import is `Filtration.Transport`. Recursively following
its actual project imports at Library commit
`b22e185743f7c318f709e14e422801f4360105d5` gives exactly these nine modules,
including this entry:

```text
Langlands.Representation.Category.Basic
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.Precomposition
Langlands.Representation.Filtration.Transport
Langlands.Representation.Induction.Definitions
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.SubquotientDefinitions
```

All eight imported project Lean/Markdown pairs are unchanged from that base.
The induction and twist definitions enter through `Filtration.Transport`;
this pair invokes only its precomposition construction. No derivative,
parabolic product, segment, classification, Whittaker or finite-length
theorem is imported.

| Inherited condition or exclusion | Check for this pair |
| --- | --- |
| Actual natural filtration, unchanged target and complete feasible families | Actual subfunctors and actual quotients are transported. All original indices and the gluing permutation are retained. The Leibniz statement and all its imported pairs are unchanged; this generic pair constructs no Leibniz filtration. |
| Arbitrary carriers, independent universes and all boundary ranks/orders | There is no rank or derivative-order parameter and no restriction on carriers. The generic transport retains all given grades, including zero grades. |
| Proved general upstream inputs; no conditional consumer replacement | Only published defining constructions and ordinary natural-isomorphism operations are used. A supplied filtration is transported; no unproved derivative or consumer proposition supplies a filtration. |
| Segment derivative, existence, Jacquet and exponent formulas; analytic classification and Ze80 formulas or criteria | No segment, derivative, Jacquet or classification module or mathematical conclusion is imported or used. |
| Unlinked, linked and juxtaposed structures, reducibility, reverse quotients, adjacent swaps, two-segment commutation, gluing, ordered socle existence and exhaustion | None of these consumer results enters the nine-module closure or the new proof terms. |
| Special-head criterion, generic segment product uniqueness, multisegment exhaustion, strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | No head, socle, multisegment, exhaustion or tempered result is an input. |
| Square-integrable classification, square-integrable or regular exhaustion and forward special essential square-integrability | No square-integrability or classification result is imported or used. |
| Two-supercuspidal nonadjacent irreducibility and full-product structure/assembly | No supercuspidal or downstream product-consumer result is an input. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker finiteness, all-character single-block finiteness and dependent mirabolic finite length | No Whittaker or mirabolic module is imported; none of these conclusions supplies a proof step. |

A recursive import and hash audit checked the complete closure and unchanged
dependency pairs. A bounded scan for inherited excluded task identifiers and
conclusion names found no matches in its Lean files. Reading the new terms
and the actual quotient and precomposition definitions gives the stronger
mathematical dependency check described above.

This focused helper leaves the all-rank actual GL derivative Leibniz theorem
open. Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
