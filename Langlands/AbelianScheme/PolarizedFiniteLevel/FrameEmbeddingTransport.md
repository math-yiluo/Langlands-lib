# Frame-normalized embeddings: flatness of the image and transport along isomorphisms

Lemmas about the predicates `Datum.IsFrameEmbedding` and `Datum.Realizes` (module
`FrameEmbedding`). All schemes lie in one universe `u`.

## Declarations

- `isIso_hom_of_iso`: the underlying scheme morphism of an isomorphism of abelian schemes is
  an isomorphism. `hom_structure`: the underlying scheme morphism of a homomorphism lies over
  the base.
- `PolarizedIso.torsionPoint_hom`: a polarized isomorphism `e : a ≅ b` carries the torsion
  point of `a` with coefficients `r` to that of `b`. Proof: `PolarizedIso.mapTuple_eq` and
  `enumerateTuple_map`.
- `subschemeι_ker_toBase`: for a closed immersion `ψ` into relative projective space over
  `S` with `ψ ≫ toBase = π`, the closed subscheme of `ψ.ker` maps to `S` by
  `inv ψ.toImage ≫ π` (Mathlib: `ψ.toImage` is an isomorphism for a closed immersion).
- `Datum.IsFrameEmbedding.flat`, `Datum.IsFrameEmbedding.locallyOfFinitePresentation`: the
  closed subscheme cut out by a frame-normalized embedding is flat and locally of finite
  presentation over the base, since the abelian scheme is smooth.
- `Datum.IsFrameEmbedding.ofPolarizedIso`: if `ψ` is a frame-normalized embedding of `b` and
  `e : PolarizedIso a b`, then `hom e.abelianIso.hom ≫ ψ` is one of `a`. The cubic condition
  uses `PolarizedIso.cubicBundlePullbackIso` and the tensor comparison of pullbacks
  (`LineBundle.pullbackTensorObjIso` with `P.preservation`); the frame conditions use
  `torsionPoint_hom`.
- `Datum.Realizes.ofPolarizedIso`: the transported embedding realizes the same family (the
  kernel is unchanged by an isomorphism, `Scheme.Hom.ker_comp_of_isIso`).

## Provenance

Internal transport-of-structure lemmas for Task 7811's reduction
(`FrameChartRepresentabilityReduction`).
