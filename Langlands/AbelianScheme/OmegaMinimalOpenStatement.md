# The open part of a weak Néron model on which extended translations are flat

The module `Langlands.AbelianScheme.OmegaMinimalOpenStatement` contains one definition, the
proposition `OmegaMinimalOpenStatement`. It states the proposition and proves nothing. The
content is derived from Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §4.3,
Lemma 1, Proposition 2 and Proposition 4 (iii), printed pp. 104–107, together with the
Jacobian criterion §2.2, Corollary 10, printed p. 41 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). The section "Correspondence with the source" explains the derivation.

## The statement

`OmegaMinimalOpenStatement.{u}` quantifies over

- a discrete valuation ring `R` with fraction field `K` (`IsDiscreteValuationRing R`,
  `IsFractionRing R K`),
- an abelian variety `B` over `K` (`AbelianScheme (Spec K)`, with its commutative group law
  `μ[B.X]`),
- a scheme `W` over `Spec R` (`W : Over (Spec R)`) such that `W ⟶ Spec R` is smooth,
  separated, locally of finite type and quasi-compact,
- an isomorphism `e : B.X ≅ (Over.pullback (Spec K ⟶ Spec R)).obj W` over `Spec K` from `B`
  to the generic fibre `W_K` of `W`,

and assumes that `W` has the weak Néron mapping property
`Langlands.AbelianScheme.WeakNeronMappingProperty R K W.hom`. These are the hypotheses of
`Langlands.AbelianScheme.TranslationExtensionModelStatement`, with a chosen isomorphism `e`
in place of the mere existence of one.

It asserts an open subscheme `U : W.left.Opens` of `W` such that

1. every point of `W` that does not lie over the closed point of `Spec R` lies in `U`;
2. some point of `U` lies over the closed point of `Spec R`;
3. for every scheme `Z` with a smooth morphism `z : Z ⟶ Spec R`, every morphism
   `a : Z_K ⟶ B` over `Spec K` from the generic fibre `Z_K` of `Z`, every open subscheme
   `V` of `Z ×_R U` (`pullback z (U.ι ≫ W.hom)`) and every morphism `v : V ⟶ W` over
   `Spec R` (`SchemeHomOver (V.ι ≫ pullback.fst z (U.ι ≫ W.hom) ≫ z) W.hom`) which on the
   generic fibre is `(z, x) ↦ e (a(z) · e⁻¹(x))`, the morphism `v` takes every point of `V`
   into `U`, and the morphism `(pr₁, v) : V ⟶ Z ×_R W`
   (`pullback.lift (V.ι ≫ pullback.fst z (U.ι ≫ W.hom)) v.1`) is flat.

The generic formula in condition 3 is stated on `S`-valued points over `Spec K`, in the same
form as condition 4 of `Langlands.AbelianScheme.TranslationExtensionProperty`: for every
scheme `S` with a morphism `k : S ⟶ Spec K` and every `p : S ⟶ V` whose composite to
`Spec R` is `k ≫ (Spec K ⟶ Spec R)`, write `z_K : S ⟶ Z_K` and `x_K : S ⟶ W_K` for the
morphisms over `Spec K` induced by `k` and by the two components of `p` (the second one
followed by the inclusion `U ⟶ W`); then `p ≫ v` is the composite of the product
`(z_K ≫ a) · (x_K ≫ e⁻¹)` in the group `S ⟶ B` (computed as
`lift (z_K ≫ a) (x_K ≫ e.inv) ≫ μ[B.X]` in the category of schemes over `Spec K`) with `e`
and the projection `W_K ⟶ W`.

The domain `V` in condition 3 is an arbitrary open subscheme of `Z ×_R U`; it need not
contain the generic fibre. The proposition contains no differential forms: these enter only
through the intended choice of `U` described below.

## Correspondence with the source

In BLR §4.3, `ω` is a left-invariant differential form of degree `d = dim B` on `B` which
generates `Ω^d_{B/K}` (BLR §4.2, Propositions 1 and 2 and Corollary 3, printed pp. 100–102).
For a smooth `R`-scheme with generic fibre `B` and a generic point `ζ` of its special fibre,
the local ring at `ζ` is a discrete valuation ring with uniformizer `π`, and `ord_ζ ω` is the
integer `n` such that `π^{-n} ω` extends to a generator of `Ω^d` at `ζ` (printed p. 104).
Lemma 1 (printed pp. 104–105) compares these orders along an `R`-rational map `u` which is
an isomorphism on generic fibres and satisfies `u^* ω = α ω` with `|α| = 1` at an integral
point: writing `u^*(π^{-n''} ω) = b · π^{-n'} ω` with `b` a regular function, one has
`n' ≥ n''`, and `u` is étale on its domain exactly when `b` is invertible, by the Jacobian
criterion §2.2, Corollary 10 (printed p. 41). Proposition 2 (printed p. 105) defines the
`ω`-minimal models as those of minimal order `n₀`, the minimum being attained on the members
of a weak Néron model. Proposition 4 (iii) (printed p. 106) asserts that over the local ring
`R'` of a smooth `R`-scheme `Z` at a generic point of its special fibre, translations of the
generic fibre by `K'`-valued points extend to `R'`-birational morphisms of the glued
`ω`-minimal model which are open immersions on their domains of definition.

`OmegaMinimalOpenStatement` is this argument for a single separated model `W` with the weak
Néron mapping property, spread out over a smooth `R`-scheme `Z`. Write `n₀` for the minimum,
over the irreducible components of the special fibre of `W`, of the order of `ω` at their
generic points. The intended `U` is the `ω`-minimal part of `W`: the open subscheme on which
the rational section `π^{-n₀} ω` of `Ω^d_{W/R}` is a regular generator. It contains the
generic fibre (condition 1) and the generic points of the `ω`-minimal components of the
special fibre, which is nonempty since the weak Néron mapping property, applied to
`T = Spec R` and the unit section of `B`, gives an `R`-valued point of `W` (condition 2).
For `v` as in condition 3, translation invariance of `ω` shows that `(pr₁, v)` pulls the
relative form `pr₂^*(π^{-n₀} ω)` of degree `d` over `Z` back to itself on `V`; on `V`, an
open subscheme of `Z ×_R U`, this form generates `Ω^d_{V/Z}`. Let `y` be a point of the
special fibre of `V` and `w = v(y)`. Near `w`, `π^{-n₀} ω = π^{n - n₀} η`, where `n ≥ n₀`
is the order of `ω` at the generic point of the component of the special fibre through `w`
and `η` generates `Ω^d_{W/R}` near `w`. Near `y`, `(pr₁, v)^* pr₂^* η = b · pr₂^*(π^{-n₀} ω)`
with `b` a regular function (the Jacobian determinant of `(pr₁, v)` relative to `Z`), so
`π^{n - n₀} b = 1` near `y`. Comparing orders as in Lemma 1 gives `n = n₀`, so `w ∈ U`, and
`b` is invertible near `y`; by the Jacobian criterion `(pr₁, v)` is étale at `y`, in
particular flat. On the generic fibre, `(pr₁, v)` is the restriction of the automorphism
`(z, x) ↦ (z, a(z) · x)` of `Z_K ×_K W_K`.

This explains the origin of the statement; the module does not prove it.

## Use

Condition 3 is the step of BLR §4.3, Proposition 4 (iii), that
`Langlands.AbelianScheme.TranslationExtensionModelStatement` needs, and conditions 1 and 2
make `U` a model of `B` that is surjective over `Spec R`. Taking `X = U` in that statement,
the weak Néron mapping property of `W`, applied to the smooth `R`-scheme `Z ×_R U` and to the
morphism `(z, x) ↦ a(z) · x` on its generic fibre, gives an extension `v` into `W` on an open
subscheme `V` of `Z ×_R U` containing the generic fibre and meeting every irreducible
component of the closed fibre; condition 3 then shows that `v` factors through `U` and that
`(pr₁, v)` is flat.
