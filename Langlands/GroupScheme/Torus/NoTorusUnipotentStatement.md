# A connected group variety without tori is unipotent: statement

Worker 1395.

`NoTorusUnipotentStatement.{u}` concerns a field `k : Type u` and a group
scheme `Q` over `Spec (CommRingCat.of k)` such that `Q.X.hom` is smooth and
affine and the underlying scheme `Q.X.left` is a connected topological space.
Suppose that for every commutative group scheme `T` over `Spec k` with
`IsTorus T.toGrp`, every homomorphism `g : T.toGrp ⟶ Q` satisfies
`SubgroupFunctor.range g = ⊥`. Then `IsUnipotent Q` holds.

This file only defines a proposition and proves nothing.

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Proposition 17.81, printed p.378 (one-based PDF p.394): "A connected group
variety is unipotent if it contains no nontrivial torus." The proposition
is stated over an arbitrary field. Milne proves it by induction on the
dimension when `k` is infinite, and by a separate argument (17.99) when `k`
is finite.

## Correspondence with the source

- In Milne, a group variety is a smooth algebraic group, that is, a smooth
  group scheme of finite type over `k` ("group variety" = "smooth
  algebraic group", after Proposition 1.26, printed p.13, one-based PDF
  p.29). `Q` is smooth and affine over `Spec k`. A smooth morphism
  is locally of finite type, and an affine scheme locally of finite type
  over a field is of finite type, so `Q` is a group variety. The statement
  covers only affine group varieties. This is a restriction of Milne's
  proposition, so the Lean statement is a special case of it.
- Connectedness is `ConnectedSpace Q.X.left`, connectedness of the
  underlying topological space, which is Milne's notion.
- `IsUnipotent Q` is the Library's definition from `Reductive.Basic`: every
  nonzero finite-dimensional matrix representation of `Q` has a nonzero
  fixed vector. This is Milne's definition 6.45 (printed p.135, one-based
  PDF p.151), as recorded in `Reductive.Basic`; every representation is a
  union of finite-dimensional subrepresentations, so testing
  finite-dimensional ones suffices.
- `IsTorus` is the Library's definition from `Torus.Lattice`: split after
  base change to some field extension of `k` (Milne, Definition 12.14,
  printed p.236, one-based PDF p.252). Tori are commutative, so letting `T`
  range over commutative group schemes loses no torus.

## Homomorphism form of "contains no nontrivial torus"

`SubgroupFunctor.range g = ⊥` says that `g` sends every point, over every
test scheme, to the identity, so `g` is the trivial homomorphism. The
hypothesis of the Lean statement therefore says that every homomorphism
from a torus over `k` to `Q` is trivial.

This hypothesis implies Milne's hypothesis. A nontrivial torus in `Q` is
an algebraic subgroup of `Q` that is a nontrivial torus. Its inclusion is
a nontrivial homomorphism from a torus to `Q`, which the Lean hypothesis
excludes. So the Lean statement follows from Proposition 17.81. The two
hypotheses are in fact equivalent, because the image of a homomorphism
from a torus is a torus (a quotient of a torus is a torus, Milne §12.e
after Definition 12.14). That converse is not needed here.

The same homomorphism form is used in the premise of
[`NoTorusBaseChangeStatement`](NoTorusBaseChangeStatement.md), whose
hypothesis is identical except that `Q` is not assumed connected.
