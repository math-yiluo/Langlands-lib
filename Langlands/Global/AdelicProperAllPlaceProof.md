# Actual all-place comparison for proper adelic scheme points

`Langlands.Global.adelicProperAllPlace` proves the unchanged
`Langlands.Global.AdelicProperAllPlaceStatement` in an arbitrary common universe.
The two component theorems are `curvePlaceProperAllPlace` and
`numberFieldProperAllPlace`. The maps are the original coefficient restriction
maps `curvePlaceAdelePointMap` and `numberFieldAdelePointMap`; their sources have
the arithmetic topology transported from the specified spread, and their targets
have the independently defined local scheme-point product topologies.

Worker 208 authored the mathematical proof in the shared draft. Worker 1568
prepared this proof pair against the published dependencies and checked it in
the pinned environment.

The hypotheses are exactly those of the target. In the function-field branch the
constant field is finite, and the original field is a finite extension of its
specified rational-function field with the given compatible scalar tower. There
is no separability restriction. The number-field branch includes every infinite
place. The supplied arithmetic model is only required to be finite type, expressed
by its locally finite-type and quasi-compact structure morphism; it can be
nonaffine and initially nonseparated. Its specified generic fiber is proper. The
initial finite set may be empty.

This is the derived proper-scheme extension of Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed p.10, Example 4.3.
The proper-spreading and valuative ingredients are those used in printed p.11,
Proposition 4.4, with the arithmetic-level topology from Section 4 and the product
comparison of Theorem 3.6. The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paper does not separately state this general proper-scheme comparison; its
derived provenance is retained in the target.

The implemented proof has four parts.

1. **Injectivity.** The actual adelic coefficient algebra injects into the product
   of its completed fields and is therefore reduced. Separated coefficient-change
   injectivity, followed by quasi-separated product-point injectivity, shows that
   the full completed-coordinate family determines an adelic scheme point. The
   number-field argument uses the sum of the infinite and finite place types and
   then compares it to the published binary product of the two point families.
2. **Continuity.** At each arithmetic level, the actual local-model comparison is
   continuous by its defining induced topology. The inverse local base-change
   homeomorphism and coefficient continuity give continuous coordinates in the
   original model's field-valued point topologies. Actual fixed-stage base-change
   equivalences transport this assertion to every stage of the original fixed
   model. The universal continuity criterion for the arithmetic final topology
   then gives continuity on full model-valued adelic points. Generic-fiber
   base-change homeomorphisms and the specified scheme isomorphism transport this
   to the independent local topologies of the requested field scheme. Explicit
   coefficient naturality and pullback-projection identities prove agreement with
   the original all-place map. This argument does not identify the arithmetic
   topology with the chart topology on points over the nonlocal adelic ring.
3. **Surjectivity.** Properness of the specified generic fiber gives properness of
   the original model's generic structure map. Apply eventual properness to the
   model morphism into the terminal relative scheme. The terminal target still
   has an isomorphism as its structure map after every base change, so this yields
   an actual finite enlargement where the model itself is proper. At that stage,
   the valuative criterion extends each completed-field point over the completed
   valuation ring outside the finite set; points inside the set and at infinite
   places are retained directly. Product-point surjectivity and the actual level
   coefficient equivalence assemble all these points. Fixed-stage and generic-
   fiber naturality identify their images with the prescribed original local
   family. Thus no proper initial model or local integrality is assumed.
4. **Homeomorphism.** Proper adelic points are compact by the existing spread
   compactness theorem. Every local scheme-point factor is Hausdorff by
   separatedness of the proper field scheme. Their full product is Hausdorff.
   Mathlib's compact-to-Hausdorff continuous-bijection criterion completes the
   homeomorphism of the actual map.

The private generic and arithmetic transport helpers are internal to this proof.
The component injectivity, continuity and surjectivity lemmas describe the same
actual maps used by the final target. This unit does not assert existence of a
supplied spread, a projective-space specialization, rational-point density, the
affine-line subspace-topology conclusion, smooth adelic openness or the
algebraic-space results of Section 5. Those remain separate parent obligations.
