# Nonzero integer multiplication on abelian schemes

`Langlands.GroupScheme.MultiplicationIsogenyStatement` is a proposition target.
For every scheme `S` and group object `G : Grp (Over S)`, assume explicitly that
`G.X` is commutative and that its structure morphism `G.X.hom` is smooth, proper,
and geometrically connected. The target says that for every integer `n ≠ 0`,
`Langlands.GroupScheme.multiplication G n` is an isogeny in the published
finite-flat-surjective convention.

Both the multiplication map and the isogeny predicate are imported from the
Library. In particular, the conclusion concerns the actual morphism of schemes
`(multiplication G n).hom.hom.left`: it asserts Mathlib's `IsFinite`, `Flat`,
and `Surjective` for that morphism. Multiplication is the pointwise integer power
of the identity group-scheme homomorphism, so it acts by `x ↦ x ^ n` on points.
The statement supplies no new scheme or morphism as data.

## Source correspondence and derived scope

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The locators below use the author's page numbers, which equal the one-based PDF
page numbers in this copy.

- Section 20, opening definition, p.42, starts with an arbitrary scheme `S`
  and defines an abelian scheme as a smooth proper group scheme with connected
  geometric fibres. These are the three geometric hypotheses in the target.
  Mathlib's `GeometricallyConnected` expresses connectedness after pullback to
  any field over the base, the usual equivalent geometric connectedness
  condition.
- Corollary 20.2(c), p.43, asserts commutativity. Here commutativity remains an
  explicit hypothesis because the imported multiplication is bundled as a
  group-scheme homomorphism using `IsCommMonObj`. This module neither proves
  commutativity nor defines a replacement notion of abelian scheme.
- Proposition 20.7 and its proof, p.44, assert finite, flat, surjective
  multiplication for an abelian scheme of relative dimension `g`. The proof
  invokes the fibrewise result of Theorem 8.2, p.13, where `n > 0` is explicit.
  The sentence of Proposition 20.7 does not itself state this restriction; our
  target explicitly excludes zero.

The provenance is **derived** for two reasons. First, the target allows negative
nonzero integers. For `n < 0`, multiplication by `n` is multiplication by `-n > 0`
composed with inversion. Inversion on a commutative group scheme is an
automorphism, and finiteness, flatness, and surjectivity are preserved by
composition with an isomorphism. This explains the intended extension; the
present file contains no proof of it.

Second, the target does not choose a globally constant relative dimension.
The finite-flat-surjective part of the proof of Proposition 20.7 uses positive
integer multiplication on each abelian-variety fibre, flatness of the abelian
scheme over its base, the fibrewise flatness criterion, and properness together
with finite fibres. These arguments do not require the dimensions of different
fibres to agree. Equivalently, one can work on base opens of constant relative
dimension and use locality of finite, flat, and surjective morphisms. The fixed
`g` in Proposition 20.7 is needed for its additional uniform order formula, which
we do not state.

There is no field, connectedness, quasicompactness, noetherian, characteristic,
or invertibility assumption on the base or on `n`, beyond `n ≠ 0`. In particular,
this target includes multiplication by the residue characteristic, and asserts
flatness rather than etaleness in that case. It asserts no degree, torsion rank,
etaleness, or inverse in a rationalized category.

## Formal status and specialization

The Lean declaration is a `Prop`-valued `def`, not a theorem or an assumption.
Its proof is a separate obligation to be assigned after this statement is
accepted and published. It already quantifies over the actual geometric data of
an abelian scheme; a later bundled abelian-scheme interface can specialize it by
passing its underlying group scheme and the four hypotheses. That specialization
must import the accepted bundle and this statement.
