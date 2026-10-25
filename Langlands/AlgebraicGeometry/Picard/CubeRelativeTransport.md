# Cube products and the relative family

This internal categorical transport module compares the chosen relative
space `T ×_S X` with the underlying scheme of the actual product `X ⨯ T`
in `Over S`. It is defined for every scheme universe and arbitrary base
scheme, without geometric hypotheses.

The construction `relativeSpaceProdIso` composes the existing
`relativeSpaceSymmetry` with the inverse of Mathlib's
`Over.prodLeftIsoPullback`. Its projection identities identify the `X`
factor with the second pullback projection and the `T` factor with
`relativeProjection`. Naturality follows by comparing these projections.
The underlying map of a section in `Over S` satisfies its ordinary
section law by the defining slice-category equation. The relative
section becomes the product map inserting this section, and hence the
published `CubeFace.first`.

`CubeFace.secondAxis` and `CubeFace.thirdAxis` are the two actual pointed
axes of `Y ⨯ Z`. The product of the identity on `X` with either axis is
the corresponding published second or third cube face. Naturality then
gives `relativeSpaceProdIso_cubeSecond` and
`relativeSpaceProdIso_cubeThird`.

All the names above are in `Langlands.AlgebraicGeometry.Picard`, with the
axis names in its `CubeFace` namespace. In particular, for
`e_T = relativeSpaceProdIso X T`, the proved scheme equations are

```text
e_T.hom ; (prod.fst).left = pullback.snd T.hom X.hom
e_T.hom ; (prod.snd).left = (relativeProjection X.hom).app T
(relativeSpace X.hom).map h ; e_U.hom
  = e_T.hom ; (prod.map (identity X) h).left
(relativeSection X.hom x₀.left (overSection_comp X x₀)).app (Y × Z) ; e_(Y × Z).hom
  = (CubeFace.first X Y Z x₀).left
(relativeSpace X.hom).map (CubeFace.secondAxis Y Z y₀) ; e_(Y × Z).hom
  = e_Z.hom ; (CubeFace.second X Y Z y₀).left
(relativeSpace X.hom).map (CubeFace.thirdAxis Y Z z₀) ; e_(Y × Z).hom
  = e_Y.hom ; (CubeFace.third X Y Z z₀).left
```

Here `;` is composition in diagram order, and `Y × Z` denotes the chosen
product in `Over S`. The inverse projection equations are also proved.
`overSection_comp X x₀` is exactly the section law supplied by `x₀.w`.
The face-map identifications use product extensionality and uniqueness of
maps to `Over.mk (identity S)`.

The actual module-sheaf adapters are in
`Langlands.AlgebraicGeometry.Picard.CubeRelativeTransport`. For a
commuting square `f ; i = j ; g`, `pullbackSquareIso` identifies
`f* (i* M)` with `j* (g* M)`. It composes the existing
`Scheme.Modules.pullbackComp`, `pullbackCongr`, and inverse
`pullbackComp` comparisons. `pullbackSquareTrivialization` composes this
isomorphism with the pullback of a specified trivialization of `g* M`,
then the existing `Langlands.Scheme.Modules.pullbackUnitIso j`. Thus its
output is an actual isomorphism with the structure-sheaf module on the
source of the square. These are constructions on module sheaves, rather
than identities of isomorphism classes.

For a line bundle `L` on `(X ⨯ T).left`, `relativeLineBundle` is the
existing `LineBundle.pullback e_T.hom` applied to `L`. It inherits local
rank one from that functor. `sectionPullbackIso` identifies the pullback
of this module along the relative section with the pullback of `L.obj`
along the actual product map inserting `x₀`. `rigidify` composes that
comparison with the supplied ordinary face trivialization and reverses
the resulting isomorphism. Its direction is consequently the one
required by `RigidifiedLineBundle.ofLineBundle`: from the structure
module to the section pullback. `restrictionPullbackIso` applies the
general square construction to the naturality equation for every
`h : T ⟶ U`.

The three cube adapters expose the intended consumer interface directly:

| Declaration | Input and result |
| --- | --- |
| `cubeRigidified` | A line bundle on `(X ⨯ (Y ⨯ Z)).left` and its ordinary first-face trivialization produce an object of `RigidifiedLineBundle.relative X.hom x₀.left (overSection_comp X x₀) (Y ⨯ Z)`. |
| `cubeSecondTrivialization` | Given that first-face trivialization and an ordinary second-face trivialization, produce an ordinary trivialization of the underlying module of the actual `relativePullback` along `CubeFace.secondAxis`. |
| `cubeThirdTrivialization` | Given the first-face and third-face trivializations, produce the analogous ordinary trivialization along `CubeFace.thirdAxis`. |
| `cubeRecoverTrivialization` | An ordinary trivialization of the carrier of `cubeRigidified` gives an ordinary trivialization of the original `L.obj`. |

The two restriction adapters are the general square construction applied
to the proved second- and third-face scheme equations. Their target
structure modules live respectively on `(relativeSpace X.hom).obj Z`
and `(relativeSpace X.hom).obj Y`. Their sources are definitionally the
carriers of the existing rigidified relative pullback functor. No
compatibility with the induced rigidifications is asserted. Converting
those ordinary trivializations into rigidified isomorphisms is a separate
adjustment step.

The recovery adapter specializes `recoverTrivialization` to `e_(Y × Z)`.
For any scheme isomorphism `i : A ≅ B`, that general construction first
identifies `M` with `i.inv* (i.hom* M)` using the inverse of
`pullbackId`, the inverse congruence comparison for `i.inv_hom_id`,
and the inverse composition comparison. It then pulls back the supplied
trivialization and uses the structure-sheaf pullback comparison for
`i.inv`. It requires no descent theorem.

The implementation is internal infrastructure derived from the universal
properties of actual categorical products and pullbacks and from the
published module-sheaf pullback comparisons. Its dependencies are
`RigidifiedLineBundle`, `LineBundlePullback`, `RelativeGeometry`, and the
published cube statement's actual `CubeFace` maps, together with their
existing Mathlib imports. No new original-source assertion is introduced.
The cube statement and its import closure are unchanged. The construction
reuses local rank-one preservation and rigidified pullback without
reimplementing tensor or coherence foundations. It establishes no Picard
representability, geometric rigidity, or geometric cube theorem.
