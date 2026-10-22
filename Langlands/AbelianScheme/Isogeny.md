# The relative isogeny predicate

For any scheme `S` and actual Mathlib group objects `G H : Grp (Over S)`,
`Langlands.GroupScheme.IsIsogeny f` means that the underlying morphism of schemes
`f.hom.hom.left` is finite, flat, and surjective. The scheme morphism property
`isogenyProperty` is the intersection of Mathlib's `IsFinite`, `Flat`, and
`Surjective`. Thus this definition asserts all three predicates, with no change
to their meanings and no extra structure supplied as data.

The base scheme and group schemes have universe `u`. There is no noetherian,
quasicompact, field, smoothness, properness, or commutativity hypothesis in this
predicate. It is defined on all group-scheme homomorphisms so that its restriction
to abelian schemes can reuse it directly. It does not construct the abelian-scheme
bundle, which is a separate dependency owned by Worker 129.

## Provenance and source correspondence

Edixhoven, van der Geer, and Moonen, *Abelian Varieties*, preliminary draft
(PDF built 8 February 2012), Chapter V, Proposition (5.2)(c) and Definition (5.3),
printed page 72 (PDF page 76), characterize an isogeny **of abelian varieties over
a field** by exactly these three properties. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The present general-base definition is a chosen extension of condition (c), as
specified in task `f0172c48-e294-4cd1-be2f-9deba8e26205`, rather than a claim that
the cited field result treats arbitrary bases or arbitrary group schemes.
Its provenance is therefore derived. No equivalence with a finite-kernel or
surjective-and-equal-dimension definition is asserted here. No invertibility in
rationalized Hom spaces is asserted. Closure under composition and arbitrary base
change will have their own precise statement and proof contribution.
