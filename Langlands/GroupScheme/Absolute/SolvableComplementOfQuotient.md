# Torus complements of a kernel with split torus quotient

This module proves two unconditional facts used to split a group scheme as a product of a
kernel and a torus. The first is a rank comparison for split tori over an infinite field. The
second is a criterion, in the spirit of Milne 2017, Proposition 2.34, for the multiplication map
of two subgroups to be an isomorphism of schemes. The last theorems combine them into the
splitting step of Milne 2017, Theorem 16.33(d).

## Rank comparison for split tori

Let `k` be a field, `𝕊 = Spec k`, and `I`, `J` finite index types.

- `splitTorus.exists_units_zpow_ne_one`: if `k` is infinite, then for every nonzero integer
  `m` there is a unit `a : kˣ` with `a ^ m ≠ 1`. Take `a` outside the finite set formed by `0`
  and the `|m|`-th roots of unity (`Polynomial.nthRoots`); then `a ^ |m| ≠ 1`, so
  `a ^ m ≠ 1` (`pow_natAbs_eq_one`).
- `splitTorus.characterRows_apply`: for `f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J`, the
  `i`-th coordinate of the row combination `characterRows f n` is
  `∑ⱼ nⱼ * characterMatrix f j i`. `characterRows` and `characterMatrix` are the Library's
  integer matrix of `f` (module `Torus/SplitMono`).
- `splitTorus.characterRows_injective_of_rationalPoints_surjective`: if `k` is infinite and
  `f` is surjective on rational points (`rationalPoints.map f`), the rows of its integer
  matrix are linearly independent over `ℤ`. Suppose `∑ⱼ nⱼ mⱼ = 0` with `n_{j₀} ≠ 0`. Choose
  `a` with `a ^ n_{j₀} ≠ 1` and a rational point `x` with `f(x) = (1, …, a, …, 1)` (`a` in
  position `j₀`). By the Library points formula `affinePointsEquiv_comp`,
  `∏ⱼ f(x)ⱼ ^ nⱼ = ∏ᵢ xᵢ ^ (∑ⱼ nⱼ mⱼᵢ) = 1`. The left side is `a ^ n_{j₀}`, a contradiction.
- `splitTorus.card_le_of_rationalPoints_surjective`: under the same hypotheses,
  `Nat.card J ≤ Nat.card I`. This follows from the injectivity of the linear map
  `characterRows f : ℤ^J → ℤ^I` (`LinearMap.finrank_le_finrank_of_injective`).
- `IsSplitTorus.isIso_of_mono_of_rationalPoints_surjective`: over an infinite field, let
  `H` and `K` be split tori. Let `f : H ⟶ K` be a homomorphism whose underlying morphism
  `f.hom.hom` is a monomorphism and which is surjective on rational points. Then `f` is an
  isomorphism of group schemes. Conjugating by the given isomorphisms with `𝔾_m^I` and
  `𝔾_m^J` keeps rational surjectivity. The rank inequality above is then the remaining
  hypothesis of the Library's `splitTorus.isIso_of_mono_of_iso`.

The infinite-field hypothesis is needed. Over `𝔽₂` every split torus has a single rational
point, so the inclusion of the trivial torus into `𝔾_m` is a monomorphism, surjective on
rational points, that is not an isomorphism.

## The complement of a kernel

Let `S` be a scheme and `s : L ⟶ R`, `u : U ⟶ R`, `q : R ⟶ D` homomorphisms of group schemes
over `S`. `subgroupMultiplication s u : L ⊗ U ⟶ R` is the Library's multiplication morphism
`(l, v) ↦ s(l) * u(v)`. `kernelι q` is the Library's actual scheme kernel of `q`
(module `CentralIsogeny/Basic`). The hypothesis
`SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u` says that on every test scheme
the points of `R` killed by `q` are exactly the points through `u`.

- `comp_subgroupMultiplication_eq`: for a point `w` of `L ⊗ U`, the composite
  `w ≫ subgroupMultiplication s u` is the product of `w ≫ fst ≫ s` and `w ≫ snd ≫ u`.
- `comp_quotient_eq_one`: under the kernel hypothesis, `y ≫ u ≫ q = 1` for every point `y`
  of `U`.
- `mono_comp_of_inf_eq_bot`: if `s` is a monomorphism and `range s ⊓ range u = ⊥` (the
  intersection is trivial on every test scheme), then `s ≫ q` is a monomorphism. For points
  `x`, `y` of `L` with equal images, `(x / y) ≫ s` is killed by `q`. It therefore lies in the
  trivial intersection, so `x = y`.
- `isIso_subgroupMultiplication_of_isIso_comp`: if `u` is a monomorphism, the kernel
  hypothesis holds, and `s ≫ q` is an isomorphism, then `subgroupMultiplication s u` is an
  isomorphism of schemes. The proof is the Yoneda criterion `isIso_of_yoneda_map_bijective`,
  with `σ = (s ≫ q)⁻¹`. Injectivity: applying `q` to `s(l) u(v) = s(l') u(v')` gives
  `(s ≫ q)(l) = (s ≫ q)(l')`, so `l = l'`; cancelling then gives `u(v) = u(v')`, so
  `v = v'`. Surjectivity: for a point `x` of `R`, put `a = σ(q(x))`. Then `s(a)⁻¹ x` is killed
  by `q`, so it is `u(b)` for a point `b` of `U`, and `x = s(a) u(b)`. This is the direction
  (⇐) of Milne 2017, Proposition 2.34, with the factors in the order `L × U`, on all test
  schemes over an arbitrary base.
- `kernelComplementIso` (definition): under the hypotheses of the previous theorem, the
  isomorphism of schemes `L ⊗ U ≅ R` whose forward morphism is `subgroupMultiplication s u`
  (`asIso`). `kernelComplementIso_hom` records this forward morphism (by `rfl`).
- `isIso_subgroupMultiplication_of_splitTorus_quotient`: over an infinite field `k`, assume
  that `L` and `D` are split tori and that `s` and `u` are monomorphisms. Assume also the
  kernel hypothesis, `range s ⊓ range u = ⊥`, and that `s ≫ q` is surjective on rational
  points. Then `subgroupMultiplication s u` is an isomorphism of schemes. Here `s ≫ q` is a
  monomorphism by `mono_comp_of_inf_eq_bot`. It is therefore an isomorphism by the rank
  comparison, and the previous theorem applies.
- `rationalPoints_surjective_comp_of_factorization`: over a commutative ring `k`, assume the
  kernel hypothesis, that every rational point of `R` is a product `u(v) * s(t)` of rational
  points of `U` and `L`, and that `q` is surjective on rational points. Then `s ≫ q` is
  surjective on rational points, because `q(u(v) * s(t)) = q(s(t))`.

The Library's `isIso_subgroupMultiplication_reverse_iff` (module `Rational/LeviMultiplication`)
converts the conclusion to the order `U × L`. That order is used by
`SolvableMaximalTorusSemidirectStatement`.

## Provenance

This is an internal helper for the proof of Milne 2017, Theorem 16.33(d) (printed p. 336):
for a maximal torus `T` of a smooth connected solvable group `G` over an algebraically closed
field, the quotient map `G ⟶ G/G_u` induces an isomorphism from `T` onto `G/G_u`, and so
`G = G_u ⋊ T` by Proposition 2.34 (printed p. 50). The second part of this module is the
scheme-level form of that use of Proposition 2.34. The first part replaces Milne's argument
for the isomorphism `T ≅ G/G_u` (Theorem 16.27, conjugacy of sections) by a weaker criterion.
A monomorphism of split tori is an isomorphism once it is surjective on rational points; this
reduces the remaining input to a statement about rational points. The rank argument with
integer character matrices is specific to this formalization.
