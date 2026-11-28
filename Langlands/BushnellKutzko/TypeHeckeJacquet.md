# Nonzero Jacquet modules from injective Hecke operators

The module `Langlands.BushnellKutzko.TypeHeckeJacquet` (namespace
`Langlands.BushnellKutzko.TypeHeckeJacquet`) proves an abstract criterion: if a compact open
subgroup `J` carrying a smooth finite-dimensional representation `ρ` has an Iwahori
factorization relative to `(U, M, U⁻)`, an element `ζ` contracts it, `ρ` is trivial on
`ζ^{r₀} (J ∩ U) ζ^{-r₀}` for some `r₀`, and for every `r` some intertwiner `Θ` at `ζ^r` makes
the Hecke operator `typeHeckeMean ρ π (ζ^r) Θ` injective on `Hom_J(ρ, π)`, then every smooth
`π` containing `ρ` has a nonzero Jacquet module along `U`. No admissibility of `π` is used.
The triviality hypothesis cannot be dropped: for the group of order two with
`J = U = G`, `M = U⁻ = {1}`, `ζ = 1` and `ρ = π` the sign character, the identity
intertwiner gives injective Hecke operators, but the coinvariants along `U` vanish.

It is the injectivity half of the proof of C. J. Bushnell and P. C. Kutzko, *The admissible
dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
(7.3.2), printed pp. 223–224, valid for smooth representations by (7.3.6)(i), printed p. 225
(PDF page = printed page + 12), in a form that works with `Hom_J(ρ, π)` and the Hecke
operators of `(J, ρ)` directly instead of the representation `λ_P` of (7.2) and the principal
lemma (7.3.1).

## Orbit means

For a representation `τ` of a group `H` (no topology):

- `map_orbitMean_of_forall_eq`: a linear map constant on a finite orbit takes that value at
  the orbit mean; `orbitMean_eq_of_orbit_eq`: orbit means depend only on the orbit;
  `orbit_apply`, `orbitMean_apply`: translating the vector does not change orbit or mean.
- `orbitMeanLinear`: the orbit mean as a linear map when all orbits are finite
  (`orbitMeanLinear_apply`).
- `orbit_comp_subset`, `finite_orbit_comp`, `finite_orbit_comp_hom`: restriction along a
  subgroup or a homomorphism shrinks orbits.
- `orbitMean_orbitMean_comp`, `orbitMean_orbitMean_of_le`: the mean over a subgroup `K`
  absorbs a preceding mean over a subgroup `N ≤ K`.
- `finite_orbit_of_isSmooth`: in a compact topological group, smooth vectors have finite
  orbits.
- `orbitMean_conj`: if `K = g K' g⁻¹`, the `K`-mean of `π(g) v` is `π(g)` applied to the
  `K'`-mean of `v`.
- `isSmooth_linHom`: for smooth `ρ` (finite-dimensional) and `σ`, the action
  `j ↦ σ(j) ∘ (-) ∘ ρ(j)⁻¹` on linear maps is smooth.

## Contractions

`IsHeckeContraction J U M Ubar ζ` collects: every `j ∈ J` is `u m l` with `u ∈ J ∩ U`,
`m ∈ J ∩ M`, `l ∈ J ∩ U⁻` (`factor`); `ζ` commutes with `J ∩ M` (`commute`); conjugation
by `ζ` sends `U` into `U`, that is `ζ x ζ⁻¹ ∈ U` for `x ∈ U` (`normalize`; only this
inclusion is assumed, not `ζ U ζ⁻¹ = U`); `ζ u ζ⁻¹ ∈ J` for `u ∈ J ∩ U` (`upper`); `ζ⁻¹ l ζ ∈ J ∩ U⁻` for
`l ∈ J ∩ U⁻` (`lower`); every `x ∈ U` has `ζ^r x ζ^{-r} ∈ J` for some `r` (`exhaust`).
`upper_pow`, `lower_pow`, `commute_pow` and `eventually_mem` give the corresponding
statements for powers.

`linHom_heckeMap_eq`: for `Θ ∈ intertwiningSpace ρ ρ x`, `Φ ∈ Hom_J(ρ, π)` and
`d ∈ J ∩ x J x⁻¹`, the map `π(x) ∘ Φ ∘ Θ` is fixed by `d` under
`ψ ↦ π(d) ∘ ψ ∘ ρ(d)⁻¹`.

## Main theorem

`not_subsingleton_coinvariants_of_heckeInjective`: let `G` be a topological group, `π` a
smooth representation of `G`, `J` a compact open subgroup, `ρ` a smooth finite-dimensional
representation of `J`, and `IsHeckeContraction J U M Ubar ζ`. Assume that `ρ` is trivial on
`ζ^{r₀} (J ∩ U) ζ^{-r₀}` for some `r₀`, and that for every `r` some
`Θ ∈ intertwiningSpace ρ ρ (ζ^r)` has `typeHeckeMean ρ π (ζ^r) Θ Φ = 0 → Φ = 0` for all
`Φ ∈ Hom_J(ρ, π)`. If some `Φ ∈ Hom_J(ρ, π)` is nonzero, then
`Jacquet.Coinvariants π U` is not a subsingleton.

Proof. Suppose the coinvariants vanish. Every vector lies in the span of the relations
`π(n) w - w` (`n ∈ U`); for such a relation, `ζ^s n ζ^{-s} ∈ J ∩ U` for all large `s`, so the
`(J ∩ U)`-mean of `π(ζ^s)(π(n) w - w)` is zero. By linearity and finite-dimensionality of the
image of `Φ`, there is `s₀` with `(J ∩ U)`-mean of `π(ζ^{s₀}) Φ(w)` zero for all `w`. Put
`r = r₀ + s₀` and take the given `Θ` for `ζ^r`. The `J`-orbit of `φ = π(ζ^r) ∘ Φ ∘ Θ` equals
its `(J ∩ U)`-orbit, because `J = (J ∩ U)(J ∩ M)(J ∩ U⁻)` and `(J ∩ M)(J ∩ U⁻)` lies in
`J ∩ ζ^r J ζ^{-r}`, which fixes `φ` (`linHom_heckeMap_eq`). The `(J ∩ U)`-mean absorbs the
mean over `N₀ = ζ^{r₀}(J ∩ U)ζ^{-r₀}`. Since `ρ` is trivial on `N₀`, evaluation at `w`
carries the `N₀`-mean of `φ` to the `N₀`-mean of `π(ζ^{r₀}) π(ζ^{s₀}) Φ(Θ w)`, which by
`orbitMean_conj` is `π(ζ^{r₀})` applied to the `(J ∩ U)`-mean of `π(ζ^{s₀}) Φ(Θ w)`, hence
zero. So `typeHeckeMean ρ π (ζ^r) Θ Φ = 0`, and the injectivity hypothesis gives `Φ = 0`.
