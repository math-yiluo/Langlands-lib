# The theorem of the square from the balanced cube

The theorem `Langlands.GroupScheme.fieldTheoremOfTheSquare` proves the exact
Library proposition
`Langlands.GroupScheme.FieldTheoremOfTheSquareStatement.{u}` for every
universe `u`. For every field `K`, a commutative group scheme `G` over
`Spec K` whose structure morphism is smooth, proper and geometrically
connected, every actual line bundle `L` on `G`, and rational points `a, b`,
it gives an actual isomorphism of module sheaves

```text
t_(a*b)^*L ⊗ L ≅ t_a^*L ⊗ t_b^*L.
```

Here `a * b` is the group law, written additively in the literature,
`t_c` is the published translation by `c`, and pullback and tensor are the
actual scheme-module constructions. The conclusion is `Nonempty` of this
isomorphism, as in the statement.

The module first proves the adapter
`fieldTheoremOfTheSquare_of_cube`, then applies it to the published theorem
`Langlands.GroupScheme.fieldCubePullback.{u}` imported from
`Langlands.AbelianScheme.FieldCubePullbackProof`. Thus the final theorem
has the Library proposition itself as its type and no cube premise.

## Implemented assembly

Fix an arbitrary universe `u`, field `K : Type u`, commutative group object `G`
over `Spec K` with smooth, proper, geometrically connected structure map,
line bundle `L`, and rational points `a, b`, as in the published statement.
In the adapter, apply the balanced cube to `T = G.X` and the three maps

```text
f = Over.mkIdTerminal.from G.X ≫ a,
g = Over.mkIdTerminal.from G.X ≫ b,
h = 𝟙 G.X.
```

The published `MumfordPicardZero.squareIso` takes that actual cube isomorphism
and produces

```text
t_b^*(t_a^*L) ⊗ L ≅ t_a^*L ⊗ t_b^*L.
```

It removes the constant pullback factors using
`MumfordPicardZero.constantIso`, whose triviality input is the published
unconditional theorem `Picard.fieldLineBundleTriviality`. That theorem
trivializes every actual line bundle on `Spec K`; it supplies no chosen
trivialization as an outer premise.

To identify the first factor with `t_(a*b)^*L`, use
`MumfordPicardZero.pullbackCompIso`. Its morphism equality is
`translation G b ≫ translation G a = translation G (a * b)`.
The implemented rewrite uses `Over.comp_left`, `points_translation`, the
definition of `translation`, `MonObj.comp_mul`, and `mul_assoc`.
Tensor this comparison with the identity of `L.obj` by `tensorIsoOf`, then
compose with `squareIso` and wrap the isomorphism in `Nonempty`.

The final application supplies the unconditional `fieldCubePullback` theorem
to the adapter. It retains every field and every universe of the published
target. Smoothness, properness and geometric connectedness enter through
that cube theorem. No projectivity, ample existence, algebraic closure,
Picard-zero condition or extra tensor-invertibility premise is used.
The published target pair and every imported pair are unchanged.

## Source and provenance

J. S. Milne, *Abelian Varieties*, corrected author version January 2, 2022,
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
Theorem 6.7, p.10, with Corollaries 6.4 and 6.5, p.9.
The retained source is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
The full retained errata page
`milne-abelian-varieties-1986-errata-2026-10-25` was read first; its listed
corrections are incorporated in this author version.

Milne applies the cube pullback formula to the identity and the two constant
maps. This implementation applies the balanced version to the two constants
and the identity, in the order required by the published `squareIso` helper.
Corollary 6.4 has inverse factors for all three pair sums; Corollary 6.5
prints its `(f+h)` factor without that inverse. The balanced cube statement
is the corrected input used here.

The adapter code is reused from the task objective's conditional proof
supplied by Worker 998 of the previous instance, which records the same
derivation in the separating-line-bundle draft by Worker 899 of the previous
instance. These are the authors of the reused adapter; their identities were
not carried into this instance. Worker 943 of the previous instance
independently recompiled that adapter; no additional code from that worker
is used here. Worker 2784 recovered the adapter, checked the current
interfaces, assembled the unconditional theorem using the published cube
proof, and wrote this documentation. The public helpers are reused by import; their existing authorship remains in their own paired
documentation.
