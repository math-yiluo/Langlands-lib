# Relative model Hom comparison over filtered algebra colimits

The theorem `spectrumModelHomColimitComparison` proves exactly
`SpectrumModelHomColimitComparison` from `SchemeLimitModelSpectrumStatement`.
Its motivating source is Conrad, *Weil and Grothendieck approaches to
adelic points*, printed pp. 5–6, Theorem 3.4(1). The proof follows the
published generic scheme-model comparison and the explicit spectrum
adapter, rather than reconstructing a separate limit argument.

For an arbitrary small filtered diagram of commutative `R`-algebras,
an actual colimit cocone, and two arbitrary scheme models over
`Spec R`, apply `modelHomColimitComparison` to `spectrumDiagram` on the
opposite index. Its objects are affine by the construction's instance.
The scheme-limit witness is constructed by `spectrumConeIsLimit` from
the algebra-colimit witness. The structural maps and compatibility
are the actual ones from the same adapter.

The equation `spectrumHomColimitMap_eq` identifies the original-index
comparison with the generic comparison composed with the proved
equivalence `spectrumHomColimitEquiv`. Composition with that equivalence
preserves injectivity and surjectivity. The generic theorem's separate
hypotheses therefore give the first two clauses unchanged:
quasi-compact source and locally finite type target for injectivity;
quasi-compact, quasi-separated source and locally finitely presented
target for surjectivity. Local finite presentation implies local finite
type, so the latter hypotheses give bijectivity as well.

Finally, apply Mathlib's `Functor.CoconeTypes.isColimit_iff` to the
actual original-index `spectrumHomCoconeTypes`. Its canonical quotient
map is definitionally `spectrumHomColimitMap`, so the bijectivity just
proved supplies an `IsColimit` witness for `spectrumHomCocone`. No
reindexing theorem for unspecified cocones or assumed colimit property
is used.

The proof preserves the target's exact universe and all hypotheses.
It proves only the fixed-model relative Hom comparison. Initial model
existence, the tail after an initial ring stage, prescribed-isomorphism
and property descent, arithmetic specializations and topology remain
separate obligations.

The Lean proof is reused unchanged from Worker 105's shared proof draft.
Worker 706 checked the source passage, the accepted spectrum and generic
comparison APIs, and the exact theorem target, and prepared this proof
unit for independent review. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The small filtered-category scope, separate weaker hypotheses and
categorical colimit witness are derived from the generic comparison and
explicit adapter; they are not additional assertions attributed to
Conrad's printed statement.
