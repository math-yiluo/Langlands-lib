# Source presentation of abelian group schemes over arbitrary fields

`Langlands.GroupScheme.FieldAbelianVarietyPresentationStatement` is a
universe-polymorphic `Prop`-valued definition. It states a derived comparison
with the source's notion of a variety and supplies no proof.

For every field `K : Type u`, every actual group object
`G : Grp (Over (Spec (CommRingCat.of K)))`, and every instance
`IsCommMonObj G.X`, the statement is

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  LocallyOfFiniteType G.X.hom ∧
  QuasiCompact G.X.hom ∧
  IsSeparated G.X.hom ∧
  Nonempty G.X.left ∧
  GeometricallyIntegral G.X.hom.
```

The field, group object, commutativity instance, and three hypotheses agree
exactly with `Langlands.GroupScheme.FieldAmpleExistenceStatement` in
`Langlands.AbelianScheme.FieldAmpleExistenceStatement`. This module imports
only Mathlib and does not use an ample-existence statement as an assumption.

## Actual clauses and their provenance

`G.X` is an actual object of the over category of `Spec K`; `G.X.left` is its
underlying scheme and `G.X.hom` its structure morphism. The conclusion is one
explicit conjunction of actual Mathlib predicates:

1. `LocallyOfFiniteType G.X.hom` asserts local finite type of the structure
   morphism.
2. `QuasiCompact G.X.hom` asserts quasi-compactness of that morphism. Together
   with the first clause, it gives finite type.
3. `IsSeparated G.X.hom` asserts separatedness over `Spec K`.
4. `Nonempty G.X.left` asserts the existence of a point of the underlying
   scheme. The actual group unit is a section over `Spec K`; evaluating it at
   a point of the nonempty spectrum of a field supplies this point.
5. `GeometricallyIntegral G.X.hom` asserts integrality after every field-valued
   base change in Mathlib's scheme universe. Integrality means reducedness and
   irreducibility, with nonemptiness included in irreducibility.

The first three clauses follow mathematically from properness: Mathlib's
`IsProper` extends `LocallyOfFiniteType` and `IsSeparated`, and universal
closedness supplies quasi-compactness. These facts still require a proof of
the named conjunction. The unit supplies the fourth clause independently of
an ample line bundle or a projective embedding. Mathlib's
`GeometricallyConnected` also includes nonempty connectedness on its
field-valued base changes.

The fifth clause is the existing separate statement
`Langlands.AbelianScheme.SmoothGeometricIntegrality` in
`Langlands.AbelianScheme.SmoothGeometricIntegralityStatement`, specialized to
`X = G.X.left` and `p = G.X.hom`. Its source route uses smoothness after every
field-valued base change to obtain local Noetherianity and regularity, hence
normality; a nonempty connected locally Noetherian normal scheme is integral.
The present contribution does not prove that prerequisite, and a statement or
unreviewed draft of it is not a proof.

## Original source correspondence

The original is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article, author corrected version January 2, 2022. It is registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
and retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
The [author's PDF](https://www.jmilne.org/math/xnotes/AVs.pdf) is the original.
The conventions and definitions on pp.2–3 and the opening of Section 20,
p.42, were read directly; printed and one-based PDF pages agree.

On p.2, Milne requires a variety to be separated and of finite type, and to
become integral over an algebraic closure. He also records integrality over
every field extension. These are the properties expressed by the first,
second, third and fifth clauses above. The group variety on pp.2–3 has an
actual rational identity, which in particular gives the fourth clause.
Section 20, p.42, presents an abelian scheme as a proper smooth group scheme
whose geometric fibres are connected, and identifies its fibres as abelian
varieties. The Lean hypotheses specialize that presentation to `Spec K`;
commutativity is retained explicitly to match the ample-existence target.
The use of every field-valued base change is Mathlib's actual convention
for the geometric predicates.

This is a derived internal comparison, not a literal proposition from Milne.
It combines the source's variety conventions and abelian-scheme presentation
with properness consequences, the actual unit section, and the existing
geometric-integrality target. It constructs no new abstract variety type or
certificate structure.

The complete retained [author errata](https://www.jmilne.org/math/articles/1986b.html)
were read, registered as
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`,
at
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
They say the corrections are incorporated in the xnotes version. The
imperfect-field correction concerns Proposition 12.1, rather than these
conventions or Section 20. No source-specific project errata note was present
in the available notes.

## Scope and remaining proof obligations

The universe `u` is arbitrary. The statement retains arbitrary characteristic,
imperfect fields and dimension zero. It adds no algebraic-closedness,
perfectness, dimension, projectivity, ample-sheaf, or geometric-integrality
premise.

After independent acceptance and publication, a separate exact-target proof
must establish the entire named proposition with no extra outer hypotheses.
It should assemble the properness consequences and the actual unit with an
accepted, published proof of `SmoothGeometricIntegrality`, coordinating with
its existing proof owner instead of duplicating that substantial prerequisite.
No projective-space or twisting-sheaf construction is needed for this
comparison. Publishing this statement proves none of its clauses and does
not discharge `FieldAmpleExistenceStatement`.
