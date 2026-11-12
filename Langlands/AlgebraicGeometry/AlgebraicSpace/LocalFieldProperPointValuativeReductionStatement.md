# Corollary 5.6 for algebraic spaces from the valuative criterion

Author: Worker 78.

`LocalFieldProperPointValuativeReductionStatement` is the implication

```
SpaceValuativeExistenceStatement.{u} → LocalFieldProperPointMapStatement.{u}
```

between two published statements of the Library. The module only states it and contains no
proof. It isolates the reduction step of the valuative route to Conrad's Corollary 5.6 for
algebraic spaces, so that the reduction and the valuative criterion can be proved
independently.

## The two statements

- `SpaceValuativeExistenceStatement` (`SpaceValuativeExistenceStatement.lean`) is the
  implication (1) ⇒ (3) of Lemma 67.42.3 (Tag 0A3Y) of the Stacks Project, chapter
  *Morphisms of Algebraic Spaces* (registered source
  `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, file `spaces-morphisms.pdf`,
  printed pp. 90–91). For every scheme `S` and every quasi-compact, separated, universally
  closed morphism `f : X ⟶ Y` of algebraic spaces over `S`, every valuation ring `A` with
  fraction field `K`, every `s : Spec A ⟶ S`, every section `x` of `X` over `Spec K` and
  every section `y` of `Y` over `Spec A` with `f(x) = y|_{Spec K}`, there is a section `a` of
  `X` over `Spec A` with `a|_{Spec K} = x` and `f(a) = y`. Its Markdown explains the
  formalization.
- `LocalFieldProperPointMapStatement` (`LocalFieldProperPointStatement.lean`) is Conrad's
  Corollary 5.6 (*Weil and Grothendieck approaches to adelic points*, 2011, registered source
  `conrad-2011-weil-grothendieck-adelic-points`, printed p.16). For every nontrivially normed
  field `K` that is locally compact, and every proper morphism `f : X ⟶ Y`
  (`IsProperMorphism f`) of quasi-separated algebraic spaces locally of finite type over
  `Spec K`, the map `RingPoints.map f : X(K) → Y(K)` is a proper map (Mathlib's
  `IsProperMap`) for the étale-chart topologies. Its Markdown explains the formalization,
  including the archimedean case.

## The statement

`LocalFieldProperPointValuativeReductionStatement` says: if
`SpaceValuativeExistenceStatement` holds in the universe `u`, then
`LocalFieldProperPointMapStatement` holds in the universe `u`. Both statements quantify over
all their data, so the implication is between the two universally quantified propositions,
not a fibrewise implication for a single morphism. The universe `u` is the universe of the
base schemes, test rings and fields of both statements.

## Provenance

The statement is derived, not quoted from a source. Conrad proves Corollary 5.6 by Chow's
lemma for algebraic spaces and the scheme case (printed p.16). The host task
(`bc24327e-c607-4b6b-937f-69ae3b0bee57`) allows instead the valuative criterion for
universally closed morphisms of algebraic spaces with a direct topological argument. This
statement records exactly that reduction step: a proper morphism is quasi-compact, separated
and universally closed (Stacks Tag 03ZM, the Library's `IsProperMorphism`), so the valuative
criterion applies to it, and the topological argument derives properness on rational points.
The intended proof applies the valuative lift over the ring of convergent germs in an
ultrapower of the local field, after base change of `f` to an affine étale chart of `Y`.
