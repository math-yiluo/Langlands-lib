# An open set closed under geometric division is closed

The module defines
`Langlands.GroupScheme.FieldGroupOpenSubgroupClosedStatement.{u}` as a
proposition. It states the assertion below and does not prove it.

For any universe `u`, let `k : Type u` be an arbitrary field and let
`G : Over (Spec (CommRingCat.of k))` have Mathlib's `GrpObj G` structure.
Here `G.left` is the underlying scheme and `G.hom` is its structure morphism
to `Spec k`. The group structure is taken in the cartesian monoidal category
`Over (Spec k)`, whose products are fibre products over `Spec k`. Assume
`LocallyOfFiniteType G.hom`. Let `U : Set G.left` be an arbitrary subset
of its underlying topological space, and assume `IsOpen U`.

The division hypothesis quantifies over every algebraically closed field
`K : Type u`, every morphism
`b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)`, and all morphisms
`p q : Over.mk b ⟶ G`. The underlying scheme morphisms `p.left` and
`q.left` are geometric points of `G.left` over `b`. Their images are single
points because the spectrum of a field has a single point. If both images
lie in `U`, expressed as `Set.range p.left ⊆ U` and
`Set.range q.left ⊆ U`, the image of `(p * q⁻¹).left` must also lie in `U`.
The multiplication and inverse here are the actual operations on
`Over.mk b ⟶ G` induced by `GrpObj G`, supplied by Mathlib's scoped
`CategoryTheory.MonObj` instances. The conclusion is `IsClosed U`.

No nonemptiness is required; the empty open set is included. The statement
neither assumes nor claims that `U` carries a subgroup scheme structure.
It uses no smoothness, commutativity, properness, reducedness or
quasi-compactness hypothesis on `G`, and no perfectness or algebraic
closedness hypothesis on `k`. The division hypothesis concerns all the
specified geometric points, with all choices of `K` and `b`; it is not
restricted to rational points over `k` or to a single algebraically closed
extension.

## Derived provenance

The classical source is The Stacks Project Authors, *The Stacks Project*,
Chapter 39, *Groupoid Schemes*, Section 39.7, Lemma 39.7.7
([Tag 047S](https://stacks.math.columbia.edu/tag/047S)), PDF page 10 of the
chapter built 2026-07-14. The registered source is
`stacks-groupoid-schemes-chapter-pdf-2026-07-14`, retained as
`Stacks Project - Groupoid Schemes chapter (PDF 2026-07-14).pdf`.
That lemma says that the image of a homomorphism of group schemes over a
field is closed if it is open. Its proof shows that the complement is open
by translating it by points in the image, using the openness result of
Lemma 39.7.2 (Tag 0B7N, PDF page 9).

The present proposition is a derived statement, not a quotation of
Lemma 39.7.7. It replaces the image of a homomorphism by an arbitrary open
subset with the stated geometric division property, and includes local
finite type to support the following geometric-point argument. The Lean
body preserves the formulation supplied by Worker 1028; this module only
records that formulation.

For the derivation rationale, take a point `y` in the closure of `U` and
an algebraic closure `K` of its residue field. This gives a `K`-point `s`
of the base change `G_K` above `y`. The projection `G_K → G` is
universally open, being a base change of a morphism to the spectrum of a
field. Consequently `s` lies in the closure of the inverse image `U_K`.
The scheme `G_K` is Jacobson because it is locally of finite type over
the algebraically closed field `K`. Every nonempty open subset therefore
contains a closed point, and such a closed point is a `K`-point.

First choose a `K`-point in the nonempty open `U_K`. Division closure
puts the identity in `U_K` and then puts inverses of its `K`-points in
`U_K`. Translation and inversion are isomorphisms, so `s · U_K⁻¹`
is an open neighbourhood of `s`. The open intersection
`U_K ∩ s · U_K⁻¹` is nonempty because `s` lies in the closure of
`U_K`. Choose a closed `K`-point `a` in that intersection. It has the
form `a = s * b⁻¹` for a `K`-point `b` in `U_K`. Thus `s = a * b`;
since `b⁻¹` is also in `U_K`, division closure places `s` in `U_K`.
It follows that `y` belongs to `U`, which explains the closedness
conclusion. This is the rationale for the statement; the module contains
no formal proof of this argument.

The imports are Mathlib interfaces for local finite type, group objects,
the cartesian structure on `Over`, and algebraically closed fields.
The statement has no dependency on any Picard open-locus or
component-constancy assertion.
