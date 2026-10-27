# Group schemes over a field are separated: proof

The theorem `Langlands.GroupScheme.fieldSeparated.{u}` has type exactly
`Langlands.GroupScheme.FieldSeparatedStatement.{u}`. For every field
`k : Type u` and every group scheme
`G : Langlands.GroupScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))`,
the structure morphism `G.X.hom : G.X.left ⟶ Spec k` is separated. The published
statement is imported unchanged. The field, the universe `u` and the group scheme
are arbitrary. The proof adds no hypothesis on `G` or on `k`.

## Route

The proof shows that the diagonal of `G.X.left ⟶ Spec k` is a base change of the
unit section `Spec k ⟶ G.X.left`. It then shows that this unit section is a
closed immersion. Closed immersions are stable under base change, so the diagonal
is a closed immersion. That is the definition of Mathlib's
`AlgebraicGeometry.IsSeparated`.

The module has two helper results and the main theorem.

### `diagonal_isPullback_unit`

This is a general lemma about any category `C` with chosen finite products
(`CartesianMonoidalCategory C`) and any group object `G` in `C`. Write
`fst G G / snd G G : G ⊗ G ⟶ G` for the division in Mathlib's group of morphisms
`G ⊗ G ⟶ G` (`MonObj.Hom.group`). This is the morphism `(x, y) ↦ x * y⁻¹`. The
lemma states that the following square is a pullback:

```
G  --lift (𝟙 G) (𝟙 G)-->  G ⊗ G
|                           |
toUnit G           fst G G / snd G G
v                           v
𝟙_ C  ---------η--------->  G
```

The square commutes. Composing the diagonal with the division gives
`𝟙 G / 𝟙 G = 1`, and the morphism `1 : G ⟶ G` is `toUnit G ≫ η` by definition
(`Hom.one_def`).

For the universal property, take a cone given by `a : T ⟶ G ⊗ G` and
`b : T ⟶ 𝟙_ C` with `a ≫ (fst G G / snd G G) = b ≫ η`. The map `b` is the
unique map `toUnit T`, so the right side is `1`. The left side is
`(a ≫ fst G G) / (a ≫ snd G G)` (`GrpObj.comp_div`). In the group of morphisms
`T ⟶ G` this gives `a ≫ fst G G = a ≫ snd G G`. The lift is `a ≫ fst G G`.
Composing it with the diagonal recovers `a`, checked on both product
projections. Its composite with `toUnit G` equals `b`, since maps to the
terminal object are unique. The lift is unique because the diagonal followed by
the first projection is the identity.

### `unit_isClosedImmersion_of_subsingleton`

Let `S` be a scheme whose underlying space has at most one point
(`[Subsingleton S]`), and let `G : Langlands.GroupScheme S`. Then the scheme
morphism `η[G.X].left : S ⟶ G.X.left` underlying the unit is a closed
immersion. The unit is a morphism in `Over S` from the monoidal unit, which is
`S` over itself by the identity. Its triangle `η[G.X].w` therefore says that
`η[G.X].left ≫ G.X.hom = 𝟙 S`, so the unit is a section of the structure
morphism. Mathlib's `AlgebraicGeometry.isClosedImmersion_of_comp_eq_id` states
that a section of a morphism to a scheme with at most one point is a closed
immersion. It gives the result directly.

This helper is retained in the general form over any base with at most one point,
because the proof uses nothing more about the base.

### `fieldSeparated`

Fix the field `k` and the group scheme `G`, and write `S` for `Spec k`. The
underlying space of `S` is `PrimeSpectrum k`, which has exactly one point because
`k` is a field. Mathlib's instance search proves `Subsingleton` for
`Spec (CommRingCat.of k)`, and the proof transfers this instance to the
statement's spelling `Scheme.Spec.obj (Opposite.op (CommRingCat.of k))`.

The proof applies `diagonal_isPullback_unit` in `C = Over S` to the group object
`G.X`. This is Mathlib's cartesian monoidal structure on `Over S` given by fibre
products, the same one that `Langlands.GroupScheme S = Grp (Over S)` uses. The
forgetful functor `Over.forget S` preserves pullbacks, so the image of the square
is a pullback square of schemes. In Mathlib's construction of this structure, the
following identifications hold definitionally (`Over.tensorObj_left`,
`Over.lift_left` and `Over.toUnit_left`, all proved by `rfl`):

- `(G.X ⊗ G.X).left` is `pullback G.X.hom G.X.hom`;
- `(lift (𝟙 G.X) (𝟙 G.X)).left` is `pullback.lift (𝟙 _) (𝟙 _) _`, which is
  `pullback.diagonal G.X.hom`;
- `(toUnit G.X).left` is `G.X.hom`.

The proof restates the mapped square in these terms with `change`. It is the
pullback square with top edge `pullback.diagonal G.X.hom`, left edge `G.X.hom`,
bottom edge `η[G.X].left` and right edge the scheme map underlying the division
morphism. By `unit_isClosedImmersion_of_subsingleton` the bottom edge is a closed
immersion. Closed immersions are stable under base change. Mathlib's
`MorphismProperty.of_isPullback`, applied to the flipped square, therefore makes
`pullback.diagonal G.X.hom` a closed immersion. This is exactly the field of
`IsSeparated G.X.hom`.

## Relation to the source

The statement cites the Stacks Project, Groupoid Schemes, Lemma 39.7.3
(Tag 047L). Its proof cites Lemma 39.6.1 to reduce separatedness of `G ⟶ S` to
the unit section `e : S ⟶ G` being a closed immersion. It then proves that `e`
is a closed immersion. The image of `e` is a closed point (Morphisms,
Lemma 29.21.2). The map `𝒪_G ⟶ e_*𝒪_S` is surjective. Schemes, Lemma 26.24.2
then applies.

The Lean proof has the same two steps but proves each one differently. The
reduction from separatedness to the unit section is the base-change argument of
`diagonal_isPullback_unit` and `fieldSeparated`, proved here directly rather
than imported. Only the needed direction is proved: a closed unit section implies
separatedness. The closed-immersion step uses Mathlib's general lemma for
sections over a base with at most one point. That lemma reduces to affine
schemes and uses surjectivity of the corresponding ring map. It does not go
through the closed-point and skyscraper-sheaf argument of the source.

Source: The Stacks Project Authors, *The Stacks Project*, Groupoid Schemes,
Section 39.7, Lemma 39.7.3 (Tag 047L), statement and proof,
<https://stacks.math.columbia.edu/tag/047L>. Registered source
`stacks-group-scheme-field-separated-047l-2026-10-22`, the HTML snapshot
retrieved 2026-10-22, SHA256
`ccfc0293f9d03d241ebc1eedf41e90008022156f5dd6d4a8c889821483acb391`.

## Authorship

Authored by Worker 810. The published statement was authored by Worker 727. The
group-object, fibre-product and closed-immersion infrastructure is Mathlib's.
