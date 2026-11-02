# Coordinate description of the dynamic unipotent subgroup of an affine group scheme

Let `R` be a commutative ring, and let `G` be a group scheme over `Spec R` whose underlying
scheme is affine (`IsAffine G.X.left`). Write `B = Γ(G, ⊤)` for its ring of global sections.
Let `χ : 𝔾_{m,Spec R} ⟶ G` be a cocharacter. The module describes points of `G` by ring maps
out of `B` and characterizes membership in the published dynamic unipotent subgroup functor
`U_G(χ)` (`Langlands.GroupScheme.Dynamic.unipotent χ`) by coefficient conditions.

The published module [`Representability`](Representability.md) proves a similar
characterization (`Corepresented.mem_unipotent_iff`), but only for group schemes presented as
`Corepresented.groupScheme F e`. The Library has no comparison between an arbitrary affine
group scheme and such a presentation. This module works directly with the canonical
isomorphism `G.X.left ≅ Spec B` (`Scheme.isoSpec`), so it applies to every affine `G`.
All declarations are in `Langlands.GroupScheme.Dynamic.AffineChart`.

## Points and their classifying ring maps

For a commutative ring `A` and a morphism `f : Spec A ⟶ Spec R`:

- `chartMap G : Spec B ⟶ Spec R` is the structure morphism of `G` read through
  `isoSpec`. `universalPoint G : Over.mk (chartMap G) ⟶ G.X` is the inverse of `isoSpec`,
  seen as a point of `G` over `Spec B`.
- `pointRing x : B ⟶ A` is the ring map classifying a point `x : Over.mk f ⟶ G.X`. It is
  `Spec.preimage` of `x.left ≫ isoSpec.hom`; `specMap_pointRing` records this.
  `hom_ext_of_pointRing` shows that points over `Spec A` are determined by it.
- `pointRing_comp` says that restricting a point along `y : Over.mk f' ⟶ Over.mk f` composes its
  classifying map with `Spec.preimage y.left`.
- `chartHom x : Over.mk f ⟶ Over.mk (chartMap G)` is `x` viewed as a morphism to `Spec B`
  over `Spec R`. `chartHom_comp_universalPoint` says that `x` is the pullback of the universal
  point along it.
- `counit G : B ⟶ R` classifies the identity point over `Spec R`. `pointRing_one` says that
  the identity point over `Spec A` is classified by `counit G ≫ Spec.preimage f`.

## The coaction

`coaction χ : B ⟶ B[T, T⁻¹]` classifies the conjugation orbit map of the universal point,
`laurentPoint (chartMap G) ≫ orbit χ (universalPoint G)`. Here `laurentPoint` and `orbit`
are the published constructions of
[`AffineExtension`](AffineExtension.md) and [`Basic`](Basic.md). As in `Representability`,
the coefficient `(coaction χ b).coeff n` plays the role of the weight-`n` component of `b`
for the `𝔾_m`-action `t · g = χ(t) g χ(t)⁻¹`.

`pointRing_laurentPoint_comp_orbit` shows that for every point `x` over `Spec A`, the orbit
map of `x` on `Spec A[T, T⁻¹]` is classified by
`coaction χ ≫ laurentCoeffMap (pointRing x)`. That is, the coaction is applied first and then
`pointRing x` is applied to each coefficient. The proof writes `x` as the pullback of the
universal point and uses the naturality lemmas `whiskerRight_orbit` and
`laurentPoint_comp_whiskerRight`.

## Extensions over the affine line

- `polynomialExtension χ x θ hθ : polynomialScheme f ⟶ G.X` turns a ring map
  `θ : B ⟶ A[X]` into a morphism over `Spec R`. It requires that `θ`, followed by the inclusion
  `A[X] ⟶ A[X, X⁻¹]`, equals `coaction χ ≫ laurentCoeffMap (pointRing x)`. The structure
  equation over `Spec R` is checked after composing with
  `Spec A[X, X⁻¹] ⟶ Spec A[X]`, using the published cancellation lemma
  `specMap_polynomialToLaurent_cancel`.
- `laurentInclusion_comp_polynomialExtension` shows that this morphism restricts to the orbit
  map of `x` on `Spec A[X, X⁻¹]`. `pointRing_polynomialExtension` shows that it is classified
  by `θ`.
- Conversely, `pointRing_comp_polynomialToLaurent` shows that every morphism
  `E : polynomialScheme f ⟶ G.X` extending the orbit map of `x` is classified by such a lift.
  `pointRing_polynomialZero_comp` shows that its value at `X = 0` is classified by
  `pointRing E` followed by evaluation at zero.

## Membership in `U_G(χ)`

`mem_unipotent_iff χ x` proves that a point `x : Over.mk f ⟶ G.X` over `Spec A` lies in
`(unipotent χ).carrier (Over.mk f)` if and only if both of the following hold:

1. for every `b : B` and every integer `n < 0`, `pointRing x ((coaction χ b).coeff n) = 0`;
2. for every `b : B`, `pointRing x ((coaction χ b).coeff 0) = Spec.preimage f (counit G b)`.

In words, the orbit map of `x` extends over the affine line exactly when the negative
coefficients vanish at `x`. The limit at `0` is then `1` exactly when the constant coefficients
agree at `x` with the counit.

The proof follows the published proof of `Corepresented.mem_unipotent_iff`. In the forward
direction, the published `laurentInclusion_comp_of_whiskerLeft` turns the extension from the
definition of `unipotent` into an extension over `Spec A[X]`. The coefficients of the
resulting polynomial lift are read off with `Corepresented.coeff_laurentCoeffMap`,
`coeff_toLaurent_of_neg` and `coeff_toLaurent_natCast`. Its value at zero is compared with
`pointRing_one`. In the converse direction, the published `polynomialLift` truncates
`coaction χ ≫ laurentCoeffMap (pointRing x)` to polynomials, since its negative coefficients
vanish. `polynomialExtension` turns this into an extension, and
`whiskerLeft_comp_of_laurentInclusion` transports it back to `Over.mk f ⊗ 𝔸¹`. Its value at
zero is identified with the identity point through `hom_ext_of_pointRing` and condition 2.

## Provenance

This is an internal, derived module. It is an auxiliary step in the proof of
`Langlands.BruhatTits.DynamicUnipotentCompactOpenContainmentStatement`, where it shows that
the rational points of `U_G(χ)` form a closed set and gives the conjugates
`χ(t) u χ(t)⁻¹` polynomial coordinates. The mathematics is the weight-space description of
`U_G(λ)` in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), Lemmas 2.1.4 and
2.1.5, printed pp. 49–51. The published [`Representability`](Representability.md) module
already formalizes and cites it for corepresented group schemes. This module transfers that
argument to an arbitrary affine group scheme, and asserts no new result from the literature.
It does not construct representing closed subschemes for `P_G(χ)`, `Z_G(χ)` or `U_G(χ)`.
