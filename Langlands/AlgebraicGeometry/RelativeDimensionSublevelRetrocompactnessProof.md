# Retrocompactness of relative local fibre dimension sublevels

Worker 105. This proof module proves the published proposition
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.RelativeDimensionSublevelProperties.{u}`
through `relativeDimensionSublevelProperties_proof`. All schemes belong to an
arbitrary universe `u`. The first conjunct assumes local finite type and the
second local finite presentation; no separation, quasi-compactness,
Noetherianity, flatness or surjectivity premise is added to either target.

## Original sources and provenance

The statement is Stacks Project Section 29.29, Lemmas 29.29.4 and 29.29.6,
registered as `stacks-fibre-constructibility-local-dimension-2026-11-04`
(SHA-256 `1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`).
The new affine compactness argument follows original Algebra Lemma 10.125.8,
tag 00QJ, registered as `stacks-sublevel-retrocompactness-2026-11-04`
(SHA-256 `049d2783fb276c48167be1787e742da1deb8b1d9dd0739d781e187e8043c2d23`).
The original retained HTML gives both the finite coefficient model and the
Noetherian compactness argument. The passage to arbitrary schemes implements
the affine-local reduction of Lemma 29.29.6 explicitly, using a finite cover
inside each compact open source subscheme.

This is a prerequisite for pure-dimensional fibre descent in Conrad,
*Weil and Grothendieck approaches to adelic points* (31 December 2011),
printed pages 5–6, Theorem 3.4(2). It does not itself establish geometric
connectedness constructibility, filtered fibre descent or whole-paper coverage.

## Implemented proof

For a finitely presented homomorphism `R → S`, choose Mathlib's finite algebra
presentation. The published `FinitePresentationStages` model at the empty
finite subset descends its finitely many coefficients to a finitely generated
integer subalgebra `R₀`, which is Noetherian. The descended quotient algebra
`S₀` is finitely presented over `R₀`, so it is also Noetherian. The canonical
map `S₀ → S`, together with the presentation's actual scalar-extension
isomorphism, supplies an algebraic pushout. The `Spec` functor gives a
cartesian square with the actual affine morphisms. The imported
`relativeDimensionSublevel_baseChange` identifies the desired sublevel on
`Spec S` with the inverse image of the corresponding sublevel on `Spec S₀`.
The imported general openness proof makes that model sublevel open;
Noetherianity makes it compact. Quasi-compactness of the affine projection
then proves compactness of its inverse image.

`isCompact_relativeDimensionSublevel_affine` transports this result along
the canonical source and target global-section spectrum isomorphisms.
The local-dimension identities for open source restriction and injective
target composition identify the sublevel exactly, and the source
homeomorphism transports compactness.

`isCompact_relativeDimensionSublevel_of_compactSpace` chooses at each source
point an affine target neighbourhood and an affine source neighbourhood
inside its inverse image. Each restricted morphism is locally finitely
presented. Its sublevel is compact by the affine result, and its image under
the open inclusion is compact. Compactness of the whole source supplies a
finite subcover; the original sublevel is exactly the finite union of these
compact images. This auxiliary lemma assumes compactness only for this
intermediate step, without any separation assumption.

`relativeDimensionSublevelRetrocompactness_proof` applies that auxiliary
lemma to the restriction over an arbitrary compact open source set `K`.
The image of the restricted sublevel is exactly the original sublevel
intersected with `K`, by open-source local-dimension invariance. Its compactness
is precisely the definition of retrocompactness. Finally,
`relativeDimensionSublevelProperties_proof` pairs this theorem with the
separately developed general openness theorem.

## Dependency boundary

The module imports the separately published
`SchemeLocalDimensionBaseChangeProof` and
`RelativeDimensionSublevelOpennessProof` by Lean name, together with the
published coefficient-model construction and pinned Mathlib. Those imports
supply base-change invariance and general openness. This pair contributes
the retrocompactness argument and the final conjunction; the imported proofs
and their transitive helpers retain their separate publications.
