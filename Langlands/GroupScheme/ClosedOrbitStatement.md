# Existence of a closed orbit

Worker 1396.

`Langlands.GroupScheme.ClosedOrbitStatement.{u}` is a definition returning
`Prop`. This module supplies no proof of it.

For every `k : Type u` with `Field k` and `IsAlgClosed k`, write
`S = Spec (CommRingCat.of k)`. The proposition quantifies over every
`G : GroupScheme S` with `Smooth G.X.hom` and `IsAffineHom G.X.hom`, and over
every `X : Over S` with `LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`.
Assuming `Nonempty X.left`, for every `a : SchemeAction G X` it asserts that there are `O : Over S`, a morphism
`j : O ⟶ X`, an action `b : SchemeAction G O` and a rational point
`x : 𝟙_ (Over S) ⟶ O` such that

- `O.left` is reduced and `j.left` is a closed immersion;
- `O.hom` is locally of finite type and quasi-compact (these follow from the
  closed immersion and are stated so that consumers need not derive them);
- `j` is equivariant on every test scheme: for all `T : Over S`,
  `g : T ⟶ G.X` and `o : T ⟶ O`, `b.act g o ≫ j = a.act g (o ≫ j)`;
- every rational point `y : 𝟙_ (Over S) ⟶ O` equals `b.act g x` for some
  rational point `g : 𝟙_ (Over S) ⟶ G.X`.

So `O` is a reduced closed subscheme of `X` stable under the action, and its
rational points form one orbit of the rational points of `G`.

Provenance (derived). Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`. In Milne an algebraic scheme over `k` is a scheme
of finite type over `k`; it need not be separated or reduced (Conventions and
notation, printed p.3, one-based PDF p.19; A.11, printed p.569, PDF p.585).
Separatedness is a separate condition (A.41, printed p.575, PDF p.591), and an
algebraic variety is an algebraic scheme that is separated and geometrically
reduced (A.44, printed p.576, PDF p.592).

Proposition 1.65(b)–(c), printed pp.26–27 (PDF pp.42–43), is stated for
algebraic schemes, so it already covers a possibly nonseparated `X`. It shows that
an orbit is locally closed and that the orbit with its reduced structure is
stable under the action. Proposition 1.66 (orbit lemma) and the remark after its
proof, printed pp.27–28 (PDF pp.43–44), state that an orbit of minimum dimension
is closed, so a closed orbit exists. That proposition is stated for a group
variety acting on a variety over an algebraically closed field.

This statement extends the scope of Proposition 1.66. The group is a smooth
affine group scheme, which is a group variety, but `X` is only of finite type,
so it may be nonseparated and nonreduced. The proof of 1.66 uses only that an
orbit is open in its closure (A.15 and 1.65(b), both for algebraic schemes), so
the complement of the orbit in its closure is closed, has smaller dimension and
is a union of orbits. Alternatively, an orbit whose closure is minimal, which
exists by the descending chain condition on closed subsets (A.14), is closed. Neither argument uses separatedness. A nonreduced `X` is
handled through `X_red`: the product of the smooth group with a reduced scheme is
reduced (A.43), so the action restricts to `X_red`, and the orbit gets its
reduced structure as in 1.65(c). Over an algebraically closed field the closed
points are the rational points, and the orbit of `x` is the image of its orbit
map. Milne's set-level statement therefore becomes the rational-point
transitivity above.
