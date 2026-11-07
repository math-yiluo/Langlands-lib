# Right-finite functions are determined by their values on cones (uniqueness in Prop. I.6.2)

Author: Worker 249.

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RightFiniteUniqueness`,
namespace `Langlands.HarishChandraSchwartz`. It imports `CoefficientIndependence` (for
Waldspurger's coefficient space `A(π)`, `coefficientFunctionSpace`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333
(`waldspurger-2003-plancherel`). Proposition I.6.2, printed p. 249 (PDF p. 15):

> Soient `f ∈ A(G)` et `P = MU` un sous-groupe parabolique semi-standard de `G`. Il existe
> un unique élément `f_P ∈ A(M)` vérifiant la propriété suivante: pour tout `m ∈ M`, il
> existe `ε > 0` tel que pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε` pour tout
> `α ∈ Σ(P)`, on ait l'égalité `δ_P(ma)^{-1/2} f(ma) = f_P(ma)`.

The uniqueness part of the proof, printed p. 250 (PDF p. 16):

> Supposons que deux éléments `f_P` et `f'_P` de `A(M)` vérifient ces conditions. Pour
> tout `m ∈ M`, les fonctions sur `A_M`
> `A ↦ f_P(ma)`, `a ↦ f'_P(ma)`
> coïncident dans un 'cône'. Comme elles sont toutes deux `A_M`-finies, elles sont égales.
> Donc `f_P(m) = f'_P(m)` pour tout `m ∈ M`.

(The first function is printed `A ↦ f_P(ma)`; it means `a ↦ f_P(ma)`.)

This module formalizes that argument. The source states it in one sentence; the proof
below, with an explicit notion of cone, is derived.

## Definitions

- `IsRightFinite A φ`, for a subgroup `A` of a group `M` and `φ : M → ℂ`: there is a
  finite-dimensional subspace `V` of `M → ℂ` containing `φ` such that
  `m ↦ ψ(m x)` lies in `V` for every `ψ ∈ V` and every `x ∈ A`. For `A = A_M` this is
  Waldspurger's "`A_M`-finie". The definition uses only right translations by `A`,
  which is the form needed for the functions `a ↦ f(ma)`.

A *cone* below is a nonempty subset `C` of the subgroup `A` with `c s ∈ C` for every
`c ∈ C` and every `s ∈ S`, where `S ⊆ A` generates `A` as a group
(`Subgroup.closure S = ⊤`). This abstracts the source's
`{a ∈ A_M : |α(a)|_F < ε for all α ∈ Σ(P)}`, which is stable under multiplication by
`S = {a ∈ A_M : |α(a)|_F ≤ 1 for all α ∈ Σ(P)}`. That this `S` generates `A_M`, and that
the cones of the source are cones in this sense, is not proved here.

## Results

- `eq_zero_of_eqOn_cone`. Hypotheses: `A` is a group; `W` is a finite-dimensional
  subspace of `A → ℂ` with `a ↦ φ(a x)` in `W` for every `φ ∈ W` and every `x ∈ A`;
  `S ⊆ A` with `Subgroup.closure S = ⊤`; `C ⊆ A` nonempty with `c s ∈ C` for `c ∈ C`,
  `s ∈ S`; `φ ∈ W` with `φ(c) = 0` for all `c ∈ C`. Conclusion: `φ = 0`.
- `isRightFinite_zero`, `IsRightFinite.add`, `IsRightFinite.smul`, `IsRightFinite.sub`:
  the right-finite functions for a fixed `A` form a subspace.
- `IsRightFinite.eq_of_eqOn_cones`. Hypotheses: `A` a subgroup of a group `M`; `f`, `f'`
  right finite for `A`; `S ⊆ A` generating `A`; for every `m ∈ M` a nonempty `C ⊆ A` with
  `C S ⊆ C` and `f(m c) = f'(m c)` for all `c ∈ C`. Conclusion: `f = f'`.
- `isRightFinite_coefficient`. Hypotheses: `π` a complex representation of a group `M` on
  any vector space `X`; `A` a subgroup; `ℓ` any linear functional on `X`; `v ∈ X` such that
  the vectors `π(a) v`, `a ∈ A`, span a finite-dimensional space. Conclusion: the coefficient
  `m ↦ ℓ(π(m) v)` is right finite for `A`.
- `isRightFinite_of_mem_coefficientFunctionSpace`. Hypotheses: `M` a group with a topology;
  `B : SmoothRep ℂ M` admissible (`IsAdmissible B.representation`: smooth, and finite
  dimensional fixed vectors for every open subgroup); `Z` a subgroup of `M` whose elements
  commute with every element of `M`; `f ∈ coefficientFunctionSpace B` (Waldspurger's
  `A(π)`). Conclusion: `f` is right finite for `Z`.
- `eq_of_mem_coefficientFunctionSpace_of_eqOn_cones` (**uniqueness in Proposition I.6.2**).
  Hypotheses: `M` a group with a topology; `Z` a subgroup of `M` whose elements commute with
  every element of `M` (for `A_M`); `f` and `f'` each in `A(π)` for some admissible
  `π : SmoothRep ℂ M` (the representations for `f` and `f'` may differ and live in
  independent universes); `S ⊆ Z` generating `Z`; for every `m ∈ M` a nonempty `C ⊆ Z` with
  `C S ⊆ C` and `f(m c) = f'(m c)` for all `c ∈ C`. Conclusion: `f = f'`.

## Proofs

`eq_zero_of_eqOn_cone`: let `W₀ ⊆ W` be the functions of `W` vanishing on `C`; it is finite
dimensional. For `s ∈ S`, right translation by `s` maps `W₀` into itself (`C s ⊆ C`) and is
injective, hence surjective on `W₀`. So translation by `s⁻¹` also maps `W₀` into itself.
The set of `x` for which translation by `x` preserves `W₀` therefore contains `S`, `S⁻¹`
and `1` and is closed under products, so it is all of `A` (`Subgroup.closure_induction''`).
For `φ ∈ W₀`, `c ∈ C` and `a ∈ A`, `φ(a)` is the value at `c` of the translate of `φ` by
`c⁻¹ a`, which lies in `W₀`, so `φ(a) = 0`.

`IsRightFinite.eq_of_eqOn_cones`: `f - f'` is right finite with a space `V`. For fixed `m`,
the image of `V` under `ψ ↦ (a ↦ ψ(m a))` is a finite-dimensional space of functions on `A`
stable under right translations, and the image of `f - f'` vanishes on the cone `C`.
`eq_zero_of_eqOn_cone` gives that this image is zero; its value at `1` is
`f(m) - f'(m)`.

`isRightFinite_coefficient`: the image of `E = span{π(a) v : a ∈ A}` under
`u ↦ (m ↦ ℓ(π(m) u))` is finite dimensional, contains the coefficient (`v = π(1) v ∈ E`),
and is stable because `π(x) E ⊆ E` for `x ∈ A` and `ℓ(π(m x) u) = ℓ(π(m) π(x) u)`.

`isRightFinite_of_mem_coefficientFunctionSpace`: `A(π)` is the supremum of the ranges of the
coefficient maps of smooth functionals; by induction over it, it suffices to treat
`m ↦ ℓ(π(m) x)`. Choose an open subgroup `U` fixing `x` (smoothness). For `z ∈ Z` and `k ∈ U`,
`π(k) π(z) x = π(z) π(k) x = π(z) x`, so `span{π(z) x}` lies in the finite-dimensional space
of `U`-fixed vectors (admissibility), and `isRightFinite_coefficient` applies. Sums are
handled by `IsRightFinite.add`.

`eq_of_mem_coefficientFunctionSpace_of_eqOn_cones` combines the last two results.

## Relation to the source and open obligations

The module proves the uniqueness argument of Proposition I.6.2 for functions in `A(M)`,
with `A_M` replaced by a central subgroup `Z` and the cones `|α(a)|_F < ε` replaced by the
abstract cones above. Not proved here: that the source's cones are cones in this sense
(`A_M` generated by `{|α(a)|_F ≤ 1}`), and the identification of `A_M` with a central
subgroup of an actual Levi subgroup. The existence part of Proposition I.6.2 is not
treated in this module.
