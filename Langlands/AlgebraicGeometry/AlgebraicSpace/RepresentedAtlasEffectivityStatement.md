# Effective descent from one target atlas

This file states the target-atlas effectivity criteria for closed immersions,
affine morphisms, open immersions and finite morphisms of algebraic spaces.
It contains statements only.

The original source is the Stacks Project, version `ed88ff78`, *Morphisms of
Algebraic Spaces*, in the registered source
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`:

- Printed pp.22–23, Lemma 12.1, Tag 03M4: equivalence of conditions (4) and
  (1) for closed and open immersions.
- Printed pp.38–39, Lemma 20.3, Tag 03WG: condition (4) implies condition
  (1), which includes representability and affineness.
- Printed pp.95–96, Lemma 45.3, Tag 03ZQ: condition (3) implies condition
  (1), for finite morphisms.

These passages were read in the retained `spaces-morphisms.pdf` through
its full mechanical text extraction. No erratum note for this source was
present at the time of authoring.

`EtaleAtlasPropertyEffectivity P` quantifies over an arbitrary base scheme
and actual algebraic spaces over it, an arbitrary space morphism, and
an actual surjective étale scheme atlas of the target. A specified scheme
projection, together with a full cartesian presheaf square, represents its
pullback along this atlas. If that projection has `P`, the conclusion is
the published relative scheme property on every represented scheme test.
That conclusion includes representability by schemes.

There is no prior representability premise on the space morphism. The
cartesian square identifies its pullback with the specified scheme on the
entire functor of points. Etaleness and surjectivity have their existing
representable scheme-test meanings, so surjectivity is geometric
surjectivity rather than surjectivity on arbitrary sets of sections. The
four specializations use the existing scheme predicates and yield exactly
the published space predicates `IsClosedImmersion`, `IsAffineMorphism`,
`IsOpenImmersion` and `IsFinite`.

This strengthens the scope of the existing `relativeProperty_of_etale_atlas`
criterion, whose original morphism is assumed representable. A proof must
establish that representability as part of effective descent. There are
no limit diagrams, finite-presentation hypotheses or assertions of limit
property descent in this statement. This is a foundational prerequisite
for using finite scheme pullbacks to prove the corresponding limit clauses.
