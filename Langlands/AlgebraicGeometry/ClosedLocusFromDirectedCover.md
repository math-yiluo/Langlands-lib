# Closed loci on a locally directed open cover

Author: Worker 344.

This is an internal construction from Mathlib's relative gluing of schemes,
universal properties of pullbacks, and Zariski locality of closed immersions.
It supports constructing a determinant locus on a basis of opens admitting
local Lie trivializations. This file does not supply those trivializations or
the determinant charts.

Fix a scheme `X : Scheme.{u}`, an open cover `𝒰`, and a property `P` of
actual morphisms `Y ⟶ X` for every `Y : Scheme.{u}`. No reduction to points,
affine tests, or reduced test schemes occurs.

`Data P 𝒰` supplies a scheme `Z i` and an actual closed immersion
`ι i : Z i ⟶ 𝒰.X i` for each cover member. Its `chart_iff` field says, for
every actual test map `g : Y ⟶ 𝒰.X i`, that a factorization through `ι i`
exists if and only if `P (g ≫ 𝒰.f i)`. These local charts are input data.
No compatibility maps between them need to be supplied.

The cover index has a category structure and the cover is locally directed
in Mathlib's sense. Thus it has compatible open transition maps, and every
point of an intersection comes from a cover member mapping to both sides.
For the global construction, the index type is `Small.{u}` and the category
is thin. The cover need not consist of affine schemes.

The additional hypothesis `hcomp` says that `P` is stable under every
precomposition: `P g` implies `P (f ≫ g)` for arbitrary scheme maps `f`.
The final factorization criterion also uses `hloc`: if `P` holds after
restriction along every member of the pullback of the supplied cover by
`g : Y ⟶ X`, then `P g`. This is a specified locality hypothesis for this
cover and its pullbacks; the file does not assert it for an arbitrary
property.

The declarations are in
`Langlands.AlgebraicGeometry.ClosedLocusFromDirectedCover.Data`.
`emb i` is the composite `ι i ≫ 𝒰.f i`. Its property follows by taking
the identity factorization in `chart_iff`. Given a transition `i ⟶ j`,
`transition` factors `ι i ≫ 𝒰.trans f` through `ι j` using the shared
criterion. Monicity of `ι j` proves the functor laws. These maps give
`functor` and the natural transformation `natTrans` of closed inclusions.

`equifibered` proves that each transition square is cartesian. A cone over
`Z j ⟶ 𝒰.X j ← 𝒰.X i` determines a map into `X` having `P` by `hcomp`.
The local criterion for `i` produces its lift into `Z i`. The lift's
second equation is its chosen factorization equation, and cancellation of
`ι j` proves the first. Cancellation of `ι i` proves uniqueness. This
constructs the pullback universal property directly.

`gluingData` packages this equifibered diagram as Mathlib
`Scheme.Cover.RelativeGluingData`. `scheme` is its actual glued scheme,
the colimit of the local pieces; `inclusion` is its actual morphism into
`X`. `isPullback` identifies each local closed immersion with the pullback
of this global morphism to the corresponding cover member. The
`IsClosedImmersion` instance for `inclusion` follows from Zariski locality
at the target: the local pullback projection is the given closed immersion
composed with an isomorphism.

`prop_inclusion` uses `hloc` to prove `P` of the global inclusion. On each
pullback cover member, the cartesian identification transports `P (emb i)`
by precomposition.

Finally, `factors_iff` proves, for every `g : Y ⟶ X`,

```
(∃ k : Y ⟶ D.scheme hcomp, k ≫ D.inclusion hcomp = g) ↔ P g.
```

A factorization implies the property by `hcomp` and `prop_inclusion`.
Conversely, restrict `g` to the pullback cover. Each restriction factors
through the corresponding `Z i` by `chart_iff`. Compose these lifts with
the maps into the glued scheme. Monicity of the global closed immersion
proves their compatibility with the directed transitions. Mathlib's
`glueMorphismsOfLocallyDirected` then gives the global lift, and cover
extensionality proves its factorization equation.

This contribution constructs a locus inside a supplied scheme from
supplied local charts. It proves no Harris moduli representability,
admissibility, smoothness, or projectivity result. Applying it to a
particular determinant condition requires constructing its cover and charts
and proving both stated properties of `P`.
