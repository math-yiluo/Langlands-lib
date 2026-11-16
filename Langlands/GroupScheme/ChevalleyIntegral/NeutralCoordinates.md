# Full coordinate torus in a relative neutral Chevalley model

This internal construction starts with a fixed integral generic closure, a represented
relative identity component `ι : N ⟶ genericModel.group`, and its defining predicate.
The full coordinate torus is geometrically connected. The published universal lifting
property therefore factors its integral map through `N`. Its composite with `ι` is the
original integral coordinate torus, and closedness descends through this open inclusion.
The construction retains every direction of the finite coordinate lattice.

When `N` has geometrically connected fibres, its relative component predicate commutes
with arbitrary base change. Each supplied field Chevalley group is smooth, affine and
connected, hence geometrically connected. Its previously constructed closed embedding
into the full field fibre factors through the neutral fibre. The factor remains closed.
Cancellation of the neutral inclusion, together with the original torus compatibility
and functoriality of base change, identifies the supplied field coordinate torus with
the base change of this single integral neutral torus.

If these neutral field embeddings are isomorphisms for every field algebra, their
inverses supply exactly `HasFieldComparisons` for the fixed neutral family and torus.
This hypothesis remains explicit; the construction alone does not assert smoothness
of the integral closure, field isomorphisms, reductivity or integral existence.
All deductions use the published component lifting, arbitrary base change, geometric
connectedness and integral coordinate comparison APIs. No new literature input is used.
