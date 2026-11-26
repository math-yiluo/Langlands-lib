# The weak Néron mapping property

The module `Langlands.AbelianScheme.WeakNeronMappingProperty` defines the weak Néron
mapping property of a scheme over a discrete valuation ring, following Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §3.5, Proposition 3, printed p. 74
(literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). It contains two definitions: the property and the proposition that
abelian varieties have models with it.

## `WeakNeronMappingProperty R K w`

Let `R` be a local ring with a field `K` and an algebra map `R → K` (in applications `R`
is a discrete valuation ring and `K` its fraction field), and `w : W ⟶ Spec R`. The
proposition says: for every scheme `T` in the same universe with a smooth morphism
`t : T ⟶ Spec R` and every morphism `uK` of generic fibres
`T ×_R Spec K ⟶ W ×_R Spec K` over `Spec K`
(`NeronModelInfra.SchemeHomOver` of the two `pullback.snd` maps), there are an open
subscheme `V` of `T` and a morphism `v : V ⟶ W` over `Spec R` such that

- every point of `T` not lying over the closed point of `Spec R` lies in `V`;
- every irreducible component of the closed fibre `{x : T // t x = closedPoint R}`
  contains a point of `V`;
- the generic fibre of `v` (`NeronModelInfra.genericFibreRestrict`) is the restriction of
  `uK` to `V ×_R Spec K`.

The generic fibre and the morphism `genericFibreRestrict` are those of the Library's
Néron mapping property `NeronModelInfra.NeronUniqueExtension`, so the two properties are
stated in the same terms.

## Correspondence with the source

BLR 2.5 (printed p. 55) calls an open subscheme `R`-dense if it is dense in every fibre
over `Spec R`, and an `R`-rational map one defined on an `R`-dense open subscheme. BLR
3.5/3 (weak Néron property): if `(X_i)` is a weak Néron model of `X_K`, `Z` a smooth
`R`-scheme with irreducible special fibre and `u_K : Z_K ⇢ X_K` a `K`-rational map, then
`u_K` extends to an `R`-rational map `u : Z ⇢ X_i` for some `i`.

The definition records this property for a single model `W` (a family with one member),
for `K`-morphisms `u_K` defined on all of `T_K`, and for every smooth `T`. These choices
are equivalent to the source's formulation for one model:

- A morphism `T ⟶ W` on an `R`-dense open of `T` that agrees with `u_K` there can be
  glued with `u_K` along the generic fibre, which is open in `T`, because `W` is
  separated and the overlap is reduced; so the open `V` may be taken to contain the
  generic fibre.
- An open subscheme containing the generic fibre is `R`-dense exactly when it meets
  every irreducible component of the closed fibre.
- For one model, the source's restriction to `Z` with irreducible special fibre is no
  restriction: apply the property to each open of `T` consisting of the generic fibre
  and the complement of all but one component of the closed fibre, and glue as above.

## `WeakNeronModelExistenceStatement`

`WeakNeronModelExistenceStatement.{u}` asserts: for every discrete valuation ring `V`
with fraction field `K` and every abelian variety `B` over `K`
(`AbelianScheme (Spec K)`), there is a scheme `W` over `Spec V`, smooth, separated,
locally of finite type and quasi-compact, with an isomorphism over `Spec K` from `B.X` to
the generic fibre `(Over.pullback (Spec K ⟶ Spec V)).obj W`, which has the weak Néron
mapping property. The module states this proposition and does not prove it.

This is BLR 3.5/2 for abelian varieties (a weak Néron model exists when `X_K(K^sh)` is
bounded, in particular when `X_K` is proper; for an abelian variety BLR take the smooth
locus of a smoothening of the schematic closure in projective space, printed p. 74)
combined with the weak Néron property 3.5/3 of the resulting single model.

## Use

The smooth locus of a smoothening of a proper flat model of an abelian variety has this
property (BLR 3.5/2 and 3.5/3; BLR 1.3, printed p. 17). It is the input of the
construction of the birational group law on `ω`-minimal models (BLR 4.3).
