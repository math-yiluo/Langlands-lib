# Rational normalizer points acting on adelic torus points

Author: Worker 2.

This internal helper module supplies the elementary identity behind the Weyl
group argument in Springer's overlap estimate (Springer, *Reduction theory over
global fields*, 1994, Proposition 2.6). A rational representative `n` of a Weyl
element satisfies `i(t) n = n i(t')` for adelic torus points. Here `t'` is the
image of `t` under the inverse of the automorphism by which `n` normalizes the
torus, so the norm of a character `χ` at `t'` is the norm of the Weyl translate
`w χ` at `t`. The provenance is derived: this is the standard relation
`t n = n (n⁻¹ t n)`, written for the Library's adelic point groups and the
published scheme-level Weyl action.

All declarations are in namespace `Langlands.Global.AdelicGroupPoints`, over a
number field `F` and a group scheme `G` over `Spec F`.

## Base points and rational points

`basePointEquiv` is the multiplicative equivalence between points
`Over.mk (𝟙 (Spec F)) ⟶ G.X` and `RationalGroupPoints F G`. Normalizer points
are stated in the first form and rational points in the second. The
equivalence precomposes with the published identification
`Lie.affineSelfTestIso` of the affine self-test scheme with the base.
Multiplicativity is `MonObj.comp_mul`. The lemmas are:

* `basePointEquiv_apply`: the defining formula, by `rfl`.
* `basePointEquiv_comp`: compatibility with group-scheme homomorphisms, i.e.
  with `affinePointsTarget`.
* `rational_basePointEquiv`: the principal adelic point of `basePointEquiv n`
  is the constant point of `n` on the adelic test scheme.

## Moving a torus point past a normalizer

`map_mul_rational_basePointEquiv`: if `n` normalizes `i : T → G` through an
automorphism `σ` of `T` (published `IsNormalizingPoint`), then

`i(t) · rational(n) = rational(n) · i(σ⁻¹ t)`

for every adelic torus point `t`. The proof combines the normalizing equation
with the published `GroupScheme.comp_innerIso_hom`. That lemma evaluates
conjugation by a constant point on the adelic test scheme.

`normCharacter_map_groupHom_inv` rewrites the norm of `χ` at `σ⁻¹ t` as the norm
of the pulled-back character `σ.inv ≫ χ` at `t`, by the published
`PositiveRealTorus.normCharacter_pullback`.

`exists_map_mul_rational_normalizer` packages both for a normalizer point
`n : normalizerPoints i`. There is an adelic torus point `t'` with
`i(t) · rational(n) = rational(n) · i(t')` and, for every character `χ`,
`|χ(t')| = |(weylAction i n χ)(t)|`. Here `|·|` is the published
`PositiveRealTorus.normCharacter`. The automorphism used is the published
`normalizingAut i n`, and `weylAction_apply` identifies the pulled-back
character with the Weyl action.
