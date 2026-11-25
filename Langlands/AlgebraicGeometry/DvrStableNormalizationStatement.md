# Stable normal models with smooth generic fibre

`Langlands.AlgebraicGeometry.DvrStableNormalizationStatement.{u}` is a
proposition definition, with no proof in this module. It records a general
scheme consequence of the Raynaud–Faltings stable-normalization theorem.
It applies to a flat, separated, finite-type scheme `X` over an arbitrary
DVR `R`, provided its actual pullback to `FractionRing R` is smooth.
Finite type is expressed by `LocallyOfFiniteType` and `QuasiCompact`.

The conclusion supplies a DVR `R' : Type u`, a flat surjective morphism
`b : Spec R' → Spec R`, and a `DvrStableNormalization.Model` of `b*X`.
The extension need not have finite degree in this interface. Every scheme
and ring remains in the original arbitrary universe `u`.

## The model data

For a scheme `X` over a DVR, `DvrStableNormalization.Model X` consists of
an actual scheme `source` over that DVR and an actual morphism
`map : source → X`, together with the following properties:

- `map` is finite and surjective.
- `source` is flat with geometrically reduced fibres over the DVR.
- The pullback of `map` to the actual fraction field is an isomorphism.
- Every positive finite fibre power of `source` has normal stalks.
- For every flat scheme `T` over the DVR whose stalks are normal, composition
  with `map` is a bijection
  `Hom(T, source) → Hom(T, X)` in the category of schemes over the DVR.

Here normal stalks means the existing `HasNormalStalks`: each actual
structure-sheaf stalk is an integrally closed domain. The definition
`positivePower source n` has `n + 1` factors, parenthesized on the left;
its zeroth term is `source` itself. The lifting clause quantifies over
all flat schemes with normal stalks, without a finite-type assumption
on the test scheme. It includes both existence and uniqueness of the
lift. It does not assert that `map` is a monomorphism on arbitrary schemes.

Local finite type, quasi-compactness and separatedness of the source
follow from the finite map and the corresponding properties of `X`;
they are not separate fields. The interface records the properties
needed below, without naming a chosen normalization construction or
asserting compatibility with every further extension.

## Provenance and source comparison

This is a derived interface from Brian Conrad's appendix to Gopal Prasad
and Jiu-Kang Yu, *On quasi-reductive group schemes*, Theorem A.2 and
Remark A.3, author-preprint p.28. Remark A.1 on the same page and the
henselian reduction used in Proposition 3.1, p.5, allow a local DVR
extension throughout. Theorem A.6, p.30, treats finiteness of normalization
without an excellence hypothesis. Corollary A.4, p.29, uses the same
normalization universal property to extend group operations.

To obtain this consequence, first pass to a faithfully flat henselian
DVR extension. Apply A.2, and take the integral closure in its finite
fraction-field extension. By A.1 this integral closure is a DVR.
Normalize the reduced base change. The generic fibre was already smooth,
so it stays smooth, reduced and normal after field extension. Thus this
normalization is an isomorphism on the generic fibre. A.2 gives a finite
normalization and geometrically reduced special fibres. Its map to the
original scheme is surjective. The normalization is flat, since its
components dominate the DVR and its coordinate rings are torsion-free.
Its generic fibre is geometrically reduced as well, so its structural
map is geometrically reduced.

Every positive fibre power is flat, with smooth generic fibre and
geometrically reduced special fibre. The normality criterion recalled in
A.3 therefore makes each such power normal. This explains the
`normal_powers` field, including the square used in A.4.

The `normal_lift` field is the usual extension consequence for a finite
map that is an isomorphism generically. For a flat test scheme, the
generic fibre is schematically dense. A map to `X` has a prescribed
lift on that generic fibre. Locally on a normal test scheme, the
coordinates of a finite cover are integral over the local ring;
their prescribed generic values lie in that ring because it is
integrally closed. These local lifts glue, and schematic density
together with separatedness of the finite map gives uniqueness.
This argument works for arbitrary flat test schemes with normal
stalks; no noetherian hypothesis on the test scheme is used.

These are scheme-level normalization and lifting assertions. No group
scheme, group law, affineness assertion, or finite smooth group-cover
conclusion appears in the proposition. Applying this prerequisite to a
group requires a separate smooth-generic reduction, construction of
the group operations and verification of the group axioms.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
file *Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf*.
