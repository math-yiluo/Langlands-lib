# Stability under generization, and the case of a nilpotent `𝔍 O_w`

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusGen`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusStd`.

## A surjectivity lemma

`surjective_of_isNilpotent_map`: let `φ : A → B` be a ring map and `𝔦` an ideal
of `A` with `𝔦B` nilpotent. If every `b ∈ B` is congruent to some `φ(a)` modulo
`𝔦B`, then `φ` is surjective.

Proof. View `B` as an `A`-module with `N` the image of `A`. The hypothesis is
`B = N + 𝔦B`, using `Ideal.smul_top_eq_map`. By induction,
`B = N + 𝔦^m B` for all `m`, since `𝔦^m N ⊆ N`. For `m` with `(𝔦B)^m = 0`
this gives `B = N`.

## Local data at `w` and at a generization

For a point `w`, `Lw 𝔍 w = O_w/𝔍O_w` is a local ring (instance from
`isLocalRing_std`). The level is `R' → O_w`, an epimorphism by
`ringHom_ext_Ow`. Its structure morphism to `Spec R` is
`Spec(O_w/𝔍O_w) → Spec R' → Spec R`.

- `wDatum R w` is the standard datum `O_w/𝔍O_w` at `w`, with `δ` the quotient
  map.
- For a generization `y` of `w` (`y.asIdeal ≤ w.asIdeal`), `genMap w y : O_w → O_y`
  is the localization map. `genDatum R w y` is the standard datum
  `O_y/𝔍O_y` at `y` for the same level `R' → O_w`, with `δ` equal to
  `O_w → O_y → O_y/𝔍O_y`.

## `infinitesimallyEtaleAt_of_le`

Let `R'` be noetherian and étale over `R`, `F` satisfy strong (F5), and the
base changes of `F` to the local schemes `Spec 𝒪_{Spec R,s}` satisfy
`UnramifiedRepresentable`. If `ξ` is infinitesimally étale at `w` and `y` is a
generization of `w`, then `ξ` is infinitesimally étale at `y`. This is Murre's
remark that the étale locus is stable under generization.

Proof. Take a level `X` for `R' → O_w` (`nonempty_level_localization`). By
`infinitesimallyEtaleAt_iff` and `van_of_killAt`, `𝔍` vanishes in the stalk of
`X` at the point `x_w` given by `wDatum`.

Let `κ : O_w/𝔍O_w → O_y/𝔍O_y` be the induced map. Then `homU` of `genDatum`
is `Spec κ` followed by `homU` of `wDatum`. Comparing elements with `map_ζ`
and `left_eq_of_elemEquiv_eq`, the point of `X` given by `genDatum` is
`mor_w ∘ Spec κ`. Hence the point `x_y` it defines is
`mor_w(Spec κ(closed point))`, a generization of `x_w`
(`specializes_closedPoint` and continuity).

By `structMap_stalkSpecializes`, the structure map at `x_y` is the structure
map at `x_w` followed by the specialization map. So `𝔍` vanishes in the stalk
at `x_y`. `killAt_of_van` for `genDatum` and `killAt_of_localization`
(`P_y ⊆ P_w`) give the lifting condition at `y` for every `β`. Then
`infinitesimallyEtaleAt_iff` gives étaleness at `y`.

## `infinitesimallyEtaleAt_of_noLargerLift`

With the same hypotheses, suppose:

- `𝔍O_w` is nilpotent;
- `NoLargerLift O_w ξ`: the restriction `restrictQuotient O_w ξ` of `ξ` to
  `Spec (O_w/𝔍O_w)` is the restriction of no element over `Spec (O_w/J)` with
  `J < 𝔍O_w`.

Then `ξ` is infinitesimally étale at `w`. This is the second half of Murre's
case (b) (printed p.252), with the local rings of the representing scheme in
place of Murre's `𝒪_F`.

Proof. Take a level `X` for `R' → O_w` and `d = wDatum R w`. Let `Λ` be the
stalk, `θ : O_w → Λ` and `ψ : Λ → O_w/𝔍O_w`, so `ψ ∘ θ` is the quotient map.

1. `θ` is surjective. By `ker_ψ_le`, `ker ψ ⊆ 𝔍O_w Λ`. So every element of
   `Λ` is congruent to an element of `θ(O_w)` modulo `𝔍O_w Λ`, and
   `𝔍O_w Λ` is nilpotent. Apply `surjective_of_isNilpotent_map`.
2. Let `Q = ker θ`. Then `Q ⊆ 𝔍O_w`, as `ψ ∘ θ` is the quotient map. The
   isomorphism `O_w/Q ≅ Λ` gives a point
   `Spec (O_w/Q) ≅ Spec Λ → X` over `Spec O_w`, hence an element
   `η ∈ F(Spec (O_w/Q))`.
3. The restriction of `η` to `Spec (O_w/𝔍O_w)` (along
   `Ideal.Quotient.factorₐ`) is `restrictQuotient O_w ξ`, which is `d.ζ`. The
   underlying morphisms agree because `factor ∘ (O_w/Q ≅ Λ)⁻¹ = ψ`; check this
   on `θ(O_w)`.
4. By `NoLargerLift`, `Q` is not strictly smaller than `𝔍O_w`, so
   `Q = 𝔍O_w`. Hence `θ` kills `𝔍`.
5. `killAt_of_van`, `killAt_of_localization` and `infinitesimallyEtaleAt_iff`
   give étaleness at `w`.

Murre's argument shows that `ψ` is an isomorphism, using completions. Here
the kernel of `ψ` is controlled by `ker_ψ_le` (formal unramifiedness and
Nakayama), and the nilpotency of `𝔍O_w` gives surjectivity of `θ` directly.
