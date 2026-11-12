# Geometric inputs for restriction of scalars

Author: Worker 110.

These are two unproved proposition definitions isolating geometric steps
in the proof of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Lemma 5.10, printed pp.17–18.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
They are derived interfaces for the source's argument, rather than
separately numbered results in the paper. This module proves neither.

Both statements quantify over arbitrary commutative rings `R` and `R'`
in a common universe and an `R`-algebra structure on `R'`, with
`Module.Finite R R'` and `Module.Projective R R'`. These express the
finite locally free hypothesis; no Noetherian, field, finite-free or
faithfulness condition is added. `X'` is an actual algebraic space over
`Spec R'`, assumed quasi-separated. No finite-type condition is imposed
on `X'` itself in either input statement.

`WeilRestrictionDiagonalStatement` asserts that the full presheaf
diagonal of the restricted fppf sheaf is representable, with every
represented scheme projection quasi-compact. If `X'` is separated, it
asserts that this full diagonal is a representable closed immersion.
The target sheaf is not already assumed to be an algebraic space.
The diagonal conditions are therefore formulated directly as relative
morphism properties, rather than as predicates on an already
constructed restricted space.

This isolates the diagonal control used in the quotient step of
Conrad's proof on printed p.18. The representability part may instead
be obtained by restricting represented equalizer loci: their
monomorphisms are separated and locally quasi-finite; quasi-compactness
allows Zariski's Main Theorem and quasi-affine Weil representability
to apply. That description is a proposed proof route, not a proof
supplied by this file. The absence of a finite-type assumption on
`X'` reflects that these are properties of its diagonal.

`WeilRestrictionAffineEtaleAtlasStatement` takes an actual affine scheme
`U'` locally of finite type over `Spec R'` and an étale surjective map
`a : schemeYoneda(U') ⟶ X'.presheaf`. It asserts that

```text
Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a
```

is étale and geometrically surjective as a transformation of full
presheaves on schemes over `Spec R`. This is exactly the transformation
of underlying presheaves induced by the sheaf Weil restriction functor.
The restricted affine source is known to be represented by the
published affine Weil scheme; target representability is not an input.

Conrad's proof on printed p.18 asserts étaleness of the restricted
atlas and its surjectivity using the decomposition of finite algebras
over strictly henselian local rings, citing EGA IV, 18.8.10. The finite
type of the atlas suffices for its affine Weil construction. Requiring
finite type of `X'` as well is unnecessary in this isolated step.
Representability and the geometric properties of this restricted
transformation remain genuine proof obligations: the statement does
not merely postulate a chosen atlas of the desired target space.

Together with affine atlas refinement, the actual affine Weil
comparison and preservation of finite presentation for the affine
representing algebra, these inputs supply the finite-type and
finite-presentation conclusions of Lemma 5.10. No proof of that
assembly or of the full lemma is claimed here.
