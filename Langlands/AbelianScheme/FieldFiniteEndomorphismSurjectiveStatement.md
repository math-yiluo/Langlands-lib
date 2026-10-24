# Surjectivity of finite abelian endomorphisms over fields

`Langlands.GroupScheme.FieldFiniteEndomorphismSurjectiveStatement` is a
`Prop`-valued definition. It states that for every field `K : Type u`, every
group object `G : Grp (Over (Spec (CommRingCat.of K)))` with
`IsCommMonObj G.X`, and every endomorphism `f : G ⟶ G`, the hypotheses

- `Smooth G.X.hom`;
- `IsProper G.X.hom`;
- `GeometricallyConnected G.X.hom`;
- `IsFinite f.hom.hom.left`

imply `Surjective f.hom.hom.left`.

Here `G.X.hom` is the structure morphism to `Spec K`. The morphism
`f.hom.hom.left : G.X.left ⟶ G.X.left` is the actual underlying morphism of
schemes. Mathlib's `IsFinite` means a finite scheme morphism: inverse images of
affine opens are affine, and the induced ring maps are finite.
`AlgebraicGeometry.Surjective` asserts surjectivity of the map on underlying
scheme points. It does not assert surjectivity on `K`-rational points.

The declaration has arbitrary universe parameter `u` and retains every field
and characteristic. There is no algebraic-closure, dimension, dominance,
positive-dimension, flatness, or surjectivity hypothesis. Finiteness is the
actual morphism predicate, with no supplied image-dimension certificate.
Commutativity is explicit. The result concerns endomorphisms over fields,
including dimension zero, and asserts only surjectivity.

## Original source and derived provenance

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Proposition 8.1 on printed/PDF p.12 and the opening definition of section 20
on printed/PDF p.42 were read directly. No source-specific errata note was
found in the project or current Library notes.

Section 20 defines an abelian scheme as a smooth proper group scheme whose
geometric fibres are connected, and relates these fibres to abelian varieties.
Over `Spec K`, the three hypotheses on `G.X.hom` give this presentation.
Mathlib's geometrically connected predicate tests connectedness after
field-valued base changes, expressing connected geometric fibres. The explicit
commutativity assumption matches the abelian group objects used by the
surrounding Library.

Proposition 8.1 states, for a homomorphism `A → B` of abelian varieties, the
equivalence of being an isogeny, having equal source and target dimensions and
being surjective, having equal dimensions and finite scheme-theoretic kernel,
and being finite, flat, and surjective. For the endomorphism here, the source
and target are the same scheme, so the dimensions agree. The kernel is the
fibre over the identity section; finiteness of the actual morphism implies
finiteness of that kernel over `K` by base change. Thus condition (c) of
Proposition 8.1 applies mathematically and yields surjectivity through (b).

This statement is a derived consequence of the source, not a separately stated
theorem in Milne. The preceding correspondence explains its provenance; it
does not supply a Lean proof. In particular, the parent
`Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement` may not be assumed
to prove this prerequisite, since that parent's proof is intended to use it.
This module does not import the parent statement.

## Separate proof obligation

This file defines the proposition and proves no instance of it. Its independent
proof obligation is to construct a theorem of this exact proposition, without
extra hypotheses or conclusion certificates.

One possible geometric route is to show that the finite morphism has closed
image of the same dimension as its source, and that a proper closed subset of
the target has strictly smaller dimension. Smoothness and geometric
connectedness over the field give geometric integrality: after extension to an
algebraic closure, the scheme is regular and locally noetherian, and connected
regular schemes have a single irreducible component; smoothness also gives
reducedness. Properness supplies finite type and quasi-compactness. The unit
section supplies nonemptiness. A formal proof following this route must justify
these assertions and every dimension comparison, including any base-change or
image construction it uses. None of that geometric machinery is assumed here.
Another valid noncircular route is permitted.

Any substantial missing prerequisites belong in separate focused tasks, with
definitions, statements, and proofs developed in dependency order after a
duplicate search. Publication of this statement alone establishes neither its
proof nor the parent finite-kernel isogeny criterion.
