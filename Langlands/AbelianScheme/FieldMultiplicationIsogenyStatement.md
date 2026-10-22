# Positive multiplication on abelian group schemes over fields

`Langlands.GroupScheme.FieldMultiplicationIsogenyStatement` is a `Prop`-valued
definition, with no proof supplied. It quantifies over every field `K : Type u`
and every actual group object `G : Grp (Over (Spec (CommRingCat.of K)))`.
Assume that `G.X` is commutative and that the structure map `G.X.hom` is smooth,
proper, and geometrically connected. For every natural number `n` with `0 < n`,
the target asserts `IsIsogeny (multiplication G (n : ℤ))`.

The two imported Library definitions retain their existing meanings.
`multiplication` is the integer power of the identity in the pointwise group of
homomorphisms; on every group of sections it sends `x` to `x ^ (n : ℤ)`, the
multiplicative notation for the usual additive multiplication by `n`.
`IsIsogeny` asserts that the actual underlying scheme morphism
`(multiplication G (n : ℤ)).hom.hom.left` is finite, flat, and surjective.
Neither the conclusion nor an auxiliary multiplication morphism is supplied
as a structure field.

## Original source and correspondence

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Printed and one-based PDF page numbers agree in this copy.

- Theorem 8.2, p.13, asserts that positive integer multiplication on an abelian
  variety over the ground field is an isogeny. Proposition 8.1, p.12, identifies
  that assertion with finiteness, flatness, and surjectivity, exactly the imported
  predicate. The theorem imposes no restriction on the characteristic for this
  conclusion.
- The conventions on p.2 define varieties to be separated finite-type schemes
  that are geometrically integral. Section 1, pp.2–3, describes their group
  objects, notes that group varieties are nonsingular, and defines abelian
  varieties by completeness and connectedness. Here completeness is properness
  over the field.
- Section 20, opening definition on p.42, describes abelian schemes by
  smoothness, properness, and connected geometric fibres, and identifies their
  fibres with abelian varieties. Over `Spec K` this gives the group schemes
  in the target. More explicitly, properness gives separatedness and finite
  type; after extension to an algebraic closure, smoothness gives regularity
  and reducedness. A connected regular noetherian scheme is irreducible,
  because its irreducible components are disjoint and open. Thus the
  geometrically connected smooth scheme is geometrically integral, as required
  by the source's convention. The identity section also guarantees nonemptiness.
  Conversely, the source's abelian varieties are smooth, proper, and
  geometrically connected group schemes. Mathlib's `GeometricallyConnected`
  tests connectedness after all field-valued base changes, an equivalent
  formulation of connected geometric fibres.
- Commutativity is explicit here because the imported bundled multiplication
  uses `IsCommMonObj`. It is consistent with the source's Corollary 2.4, p.3,
  and Corollary 20.2(c), p.43. This file does not prove commutativity or the
  equivalence of the two presentations of abelian varieties.
- Theorem 7.1, p.10, proves projectivity, and Corollary 7.2, p.12, supplies a
  symmetric ample invertible sheaf. These are consequences used in the source's
  proof of Theorem 8.2, not additional hypotheses of this target.

The provenance is derived: this is the finite-flat-surjective part of
Theorem 8.2, expressed through Proposition 8.1 and the group-scheme presentation
on p.42. Replacing a positive integer by a positive natural number and casting
to `ℤ` preserves precisely its positive range.

## Scope and proof boundary

There is no algebraic-closure, perfectness, characteristic, dimension,
projectivity, or ample-bundle assumption. In particular, the target includes
positive characteristic dividing `n`. It asserts no degree formula or etaleness,
and excludes zero explicitly. It concerns only fields and positive natural
numbers; arbitrary bases and negative integers belong to the separate published
`MultiplicationIsogenyStatement`.

A separate proof task must prove this exact Library proposition after
publication. Substantial geometric prerequisites, such as the projectivity and
line-bundle arguments used in Milne's proof, must be separated into focused
tasks if that route is pursued. This statement does not claim those prerequisites
are already formalized.
